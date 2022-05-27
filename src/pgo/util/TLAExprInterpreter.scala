package pgo.util

import pgo.model.{DefinitionOne, RefersTo, SourceLocation}
import pgo.model.tla._
import pgo.parser.TLAParser
import Description._
import pgo.trans.PCalRenderPass

import scala.annotation.tailrec
import scala.collection.View
import scala.util.control.NonFatal
import scala.util.{Failure, Success, Try}

object TLAExprInterpreter {
  private def mkExceptionDesc(reason: Description, badValue: Option[TLAValue], badNode: Option[TLANode]): Description =
    d"evaluation error ($reason)${
      badValue match {
        case None => d""
        case Some(badValue) =>
          d", due to value ${badValue.describe}"
      }
    }${
      badNode match {
        case None => d""
        case Some(badNode) =>
          d" at ${badNode.sourceLocation.longDescription}"
            .ensureLineBreakBefore
            .indented
      }
    }"

  final case class Unsupported() extends RuntimeException("unsupported") {
    private var _badNode: Option[TLANode] = None
    def badNode: Option[TLANode] = _badNode

    private var _hint: Option[Description] = None
    def hint: Option[Description] = _hint

    def ensureNodeInfo(node: TLANode): this.type = {
      _badNode = _badNode.orElse(Some(node))
      this
    }

    def ensureHint(hint: Description): this.type = {
      _hint = _hint.orElse(Some(hint))
      this
    }

    def describe: Description =
      mkExceptionDesc(
        reason = d"operation not supported by current configuration ${hint.map(h => d"[$h]").getOrElse(d"")}",
        badValue = None,
        badNode = badNode)
  }
  final case class TypeError() extends RuntimeException("TLA+ type error") {
    private var _badValue: Option[TLAValue] = None
    private var _badNode: Option[TLANode] = None
    def badValue: Option[TLAValue] = _badValue
    def badNode: Option[TLANode] = _badNode

    def ensureNodeInfo(node: TLANode): this.type = {
      _badNode = _badNode.orElse(Some(node))
      this
    }

    def ensureValueInfo(value: TLAValue): this.type = {
      _badValue = _badValue.orElse(Some(value))
      this
    }

    def describe: Description =
      mkExceptionDesc(d"TLA+ type error", badValue, badNode)
  }

  sealed abstract class TLAValue {
    final override def toString: String =
      describe.linesIterator.mkString("\n")
    def describe: Description
  }
  object TLAValue {
    def parseFromString(str: String): TLAValue = {
      val expr = TLAParser.readExpression(
        new SourceLocation.UnderlyingString(str),
        str,
        // Integers needed for prefix `-`, and TLC needed for `:>` and `@@`
        definitions = BuiltinModules.Integers.members ::: BuiltinModules.TLC.members)
      interpret(expr)(Map.empty)
        .assumeUnambiguousSuccess
    }
  }

  final case class TLAValueModel(name: String) extends TLAValue {
    override def describe: Description =
      name.toDescription
  }
  final case class TLAValueBool(value: Boolean) extends TLAValue {
    override def describe: Description =
      if (value) {
        d"TRUE"
      } else {
        d"FALSE"
      }
  }
  final case class TLAValueNumber(value: Int) extends TLAValue {
    override def describe: Description =
      value.toString.description
  }
  final case class TLAValueString(value: String) extends TLAValue {
    override def describe: Description =
      PCalRenderPass.describeExpr(TLAString(value))
  }
  final case class TLAValueSet(value: Set[TLAValue]) extends TLAValue {
    override def describe: Description =
      d"{${
        value.view
          .map(_.describe)
          .separateBy(d", ")
      }}"
  }
  final case class TLAValueTuple(value: Vector[TLAValue]) extends TLAValue {
    override def describe: Description =
      d"<<${
        value.view
          .map(_.describe)
          .separateBy(d", ")
      }>>"
  }
  final case class TLAValueFunction(value: Map[TLAValue,TLAValue]) extends TLAValue {
    value.foreach {
      case (TLAValueTuple(tuple), _) => assert(tuple.size != 1)
      case _ =>
    }

    override def describe: Description = {
      d"(${
        val result = value.view
          .map {
            case (key, value) =>
              d"\n${key.describe} :> ${value.describe}"
                .indented
          }
          .separateBy(d" @@ ")

        if(value.nonEmpty) {
          result.ensureLineBreakAfter
        } else {
          result
        }
      })"
    }
  }

  final case class TLAValueLambda(fn: PartialFunction[List[TLAValue],TLAValue]) extends TLAValue {
    override def describe: Description = d"LAMBDA ${String.format("%x", System.identityHashCode(fn))}"
  }

  private[pgo] def valueFn[T](fn: PartialFunction[TLAValue,T]): TLAValue => T =
    fn.orElse { (badValue: TLAValue) =>
      throw TypeError().ensureValueInfo(badValue)
    }

  private[pgo] final implicit class TLAValueOps(value: TLAValue) {
    def narrowMatch[T](fn: PartialFunction[TLAValue,T]): T =
      fn.applyOrElse(value, { (badValue: TLAValue) =>
        throw TypeError().ensureValueInfo(badValue)
      })
  }

  private[pgo] final implicit class TLANodeOps[N <: TLANode](node: N) {
    def narrowMatch[T](fn: PartialFunction[N,T]): T =
      fn.applyOrElse(node, { (badNode: TLANode) =>
        throw Unsupported().ensureNodeInfo(badNode)
      })
  }

  lazy val builtinOperators: Map[ById[DefinitionOne],PartialFunction[List[TLAValue],TLAValue]] =
    View[(DefinitionOne,PartialFunction[List[TLAValue],TLAValue])](
      BuiltinModules.Intrinsics.memberSym(TLASymbol.LogicalAndSymbol) -> {
        case List(TLAValueBool(lhs), TLAValueBool(rhs)) => TLAValueBool(lhs && rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.LogicalOrSymbol) -> {
        case List(TLAValueBool(lhs), TLAValueBool(rhs)) => TLAValueBool(lhs || rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.LogicalNotSymbol) -> {
        case List(TLAValueBool(op)) => TLAValueBool(!op)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.ImpliesSymbol) -> {
        case List(TLAValueBool(lhs), TLAValueBool(rhs)) => TLAValueBool(!lhs || rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.EquivSymbol) -> {
        case List(TLAValueBool(lhs), TLAValueBool(rhs)) => TLAValueBool(lhs == rhs)
      },
      BuiltinModules.Intrinsics.memberAlpha("TRUE") -> {
        case Nil => TLAValueBool(true)
      },
      BuiltinModules.Intrinsics.memberAlpha("FALSE") -> {
        case Nil => TLAValueBool(false)
      },
      BuiltinModules.Intrinsics.memberAlpha("BOOLEAN") -> {
        case Nil => TLAValueSet(Set(TLAValueBool(true), TLAValueBool(false)))
      },

      BuiltinModules.Intrinsics.memberSym(TLASymbol.EqualsSymbol) -> {
        case List(lhs, rhs) => TLAValueBool(lhs == rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.NotEqualsSymbol) -> {
        case List(lhs, rhs) => TLAValueBool(lhs != rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.InSymbol) -> {
        case List(lhs, TLAValueSet(rhs)) => TLAValueBool(rhs.contains(lhs))
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.NotInSymbol) -> {
        case List(lhs, TLAValueSet(rhs)) => TLAValueBool(!rhs.contains(lhs))
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.IntersectSymbol) -> {
        case List(TLAValueSet(lhs), TLAValueSet(rhs)) => TLAValueSet(lhs & rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.UnionSymbol) -> {
        case List(TLAValueSet(lhs), TLAValueSet(rhs)) => TLAValueSet(lhs | rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.SubsetOrEqualSymbol) -> {
        case List(TLAValueSet(lhs), TLAValueSet(rhs)) => TLAValueBool(lhs.subsetOf(rhs))
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.BackslashSymbol) -> {
        case List(TLAValueSet(lhs), TLAValueSet(rhs)) => TLAValueSet(lhs.diff(rhs))
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.PrefixUnionSymbol) -> {
        case List(TLAValueSet(set)) => TLAValueSet(set.subsets().map(TLAValueSet).toSet)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.PrefixUnionSymbol) -> {
        case List(TLAValueSet(set)) =>
          TLAValueSet(set.view
            .flatMap(valueFn {
              case TLAValueSet(memberSet) => memberSet
            })
            .toSet)
      },

      BuiltinModules.Intrinsics.memberSym(TLASymbol.DomainSymbol) -> {
        case List(TLAValueFunction(fn)) => TLAValueSet(fn.keySet)
      },

      BuiltinModules.Intrinsics.memberAlpha("STRING") -> { case Nil => throw Unsupported() },

      BuiltinModules.Intrinsics.memberSym(TLASymbol.PrimeSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.EnabledSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.UnchangedSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.CDotSymbol) -> { _ => throw Unsupported() },

      BuiltinModules.Intrinsics.memberSym(TLASymbol.TLAlwaysSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.TLEventuallySymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.SequencingSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.PlusArrowSymbol) -> { _ => throw Unsupported() },

      BuiltinModules.TLC.memberAlpha("Print") -> { case List(_, _) => throw Unsupported() },
      BuiltinModules.TLC.memberAlpha("PrintT") -> { case List(_) => throw Unsupported() },
      BuiltinModules.TLC.memberAlpha("Assert") -> {
        case List(TLAValueBool(cond), out) =>
          require(cond, out.toString)
          TLAValueBool(true)
      },
      BuiltinModules.TLC.memberAlpha("JavaTime") -> { case Nil => throw Unsupported() },
      BuiltinModules.TLC.memberSym(TLASymbol.ColonGreaterThanSymbol) -> {
        case List(lhs, rhs) => TLAValueFunction(Map(lhs -> rhs))
      },
      BuiltinModules.TLC.memberSym(TLASymbol.DoubleAtSignSymbol) -> {
        case List(TLAValueFunction(lhs), TLAValueFunction(rhs)) => TLAValueFunction(lhs ++ rhs)
      },
      BuiltinModules.TLC.memberAlpha("Permutations") -> { _ => throw Unsupported() },
      BuiltinModules.TLC.memberAlpha("SortSeq") -> { _ => throw Unsupported() },
      BuiltinModules.TLC.memberAlpha("ToString") -> {
        case List(value: TLAValue) => TLAValueString(value.describe.linesIterator.mkString("\n"))
      },

      BuiltinModules.Sequences.memberAlpha("Seq") -> {
        case List(TLAValueSet(elems)) =>
          TLAValueSet(elems.toVector.permutations.map(TLAValueTuple).toSet)
      },
      BuiltinModules.Sequences.memberAlpha("Len") -> {
        case List(TLAValueTuple(elems)) => TLAValueNumber(elems.size)
      },
      BuiltinModules.Sequences.memberSym(TLASymbol.OSymbol) -> {
        case List(TLAValueTuple(lhs), TLAValueTuple(rhs)) => TLAValueTuple(lhs ++ rhs)
      },
      BuiltinModules.Sequences.memberAlpha("Append") -> {
        case List(TLAValueTuple(elems), elem) => TLAValueTuple(elems :+ elem)
      },
      BuiltinModules.Sequences.memberAlpha("Head") -> {
        case List(TLAValueTuple(elems)) =>
          require(elems.nonEmpty)
          elems.head
      },
      BuiltinModules.Sequences.memberAlpha("Tail") -> {
        case List(TLAValueTuple(elems)) =>
          require(elems.nonEmpty)
          TLAValueTuple(elems.tail)
      },
      BuiltinModules.Sequences.memberAlpha("SubSeq") -> {
        case List(TLAValueTuple(_), TLAValueNumber(from), TLAValueNumber(to)) if from > to =>
          TLAValueTuple(Vector.empty)
        case List(TLAValueTuple(elems), TLAValueNumber(from1), TLAValueNumber(to1)) =>
          val from = from1 - 1
          val to = to1 - 1
          require(from >= 0 && to >= 0 && from < elems.size && to < elems.size)
          TLAValueTuple(elems.slice(from, to + 1))
      },
      BuiltinModules.Sequences.memberAlpha("SelectSeq") -> { _ => throw Unsupported() },

      BuiltinModules.FiniteSets.memberAlpha("IsFiniteSet") -> {
        case List(TLAValueSet(_)) => TLAValueBool(true)
      },
      BuiltinModules.FiniteSets.memberAlpha("Cardinality") -> {
        case List(TLAValueSet(set)) => TLAValueNumber(set.size)
      },

      BuiltinModules.Bags.memberAlpha("IsABag") -> { case List(_) => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("BagToSet") -> { case List(_) => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("SetToBag") -> { case List(_) => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("BagIn") -> { case List(_, _) => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("EmptyBag") -> { case Nil => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("CopiesIn") -> { case List(_, _) => throw Unsupported() },
      BuiltinModules.Bags.memberSym(TLASymbol.OPlusSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Bags.memberSym(TLASymbol.OMinusSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("BagUnion") -> { case List(_) => throw Unsupported() },
      BuiltinModules.Bags.memberSym(TLASymbol.SquareSupersetOrEqualSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("SubBag") -> { case List(_) => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("BagOfAll") -> { case List(_, _) => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("BagCardinality") -> { case List(_) => throw Unsupported() },

      BuiltinModules.Peano.memberAlpha("PeanoAxioms") -> { case List(_, _, _) => throw Unsupported() },
      BuiltinModules.Peano.memberAlpha("Succ") -> { case Nil => throw Unsupported() },
      BuiltinModules.Peano.memberAlpha("Nat") -> { case Nil => throw Unsupported() },
      BuiltinModules.Peano.memberAlpha("Zero") -> { case Nil => TLAValueNumber(0) },

      BuiltinModules.ProtoReals.memberAlpha("IsModelOfReals") -> { case List(_, _, _, _) => throw Unsupported() },
      BuiltinModules.ProtoReals.memberAlpha("RM") -> { case Nil => throw Unsupported() },
      BuiltinModules.ProtoReals.memberAlpha("Real") -> { case Nil => throw Unsupported() },
      BuiltinModules.ProtoReals.memberAlpha("Infinity") -> { case Nil => throw Unsupported() },
      BuiltinModules.ProtoReals.memberAlpha("MinusInfinity") -> { case Nil => throw Unsupported() },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.PlusSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) => TLAValueNumber(math.addExact(lhs, rhs))
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.AsteriskSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) => TLAValueNumber(math.multiplyExact(lhs, rhs))
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.LessThanOrEqualSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) => TLAValueBool(lhs <= rhs)
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.MinusSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) => TLAValueNumber(math.subtractExact(lhs, rhs))
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.SlashSymbol) -> { case List(_, _) => throw Unsupported() },
      BuiltinModules.ProtoReals.memberAlpha("Int") -> { case Nil => throw Unsupported() },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.SuperscriptSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          // don't silently truncate overflows; fail with error
          val result = math.pow(lhs, rhs)
          require(result <= Int.MaxValue && result >= Int.MinValue)
          TLAValueNumber(result.toInt)
      },

      BuiltinModules.Naturals.memberSym(TLASymbol.GreaterThanOrEqualSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) => TLAValueBool(lhs >= rhs)
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.LessThanSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) => TLAValueBool(lhs < rhs)
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.GreaterThanSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) => TLAValueBool(lhs > rhs)
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.DotDotSymbol) -> {
        case List(TLAValueNumber(from), TLAValueNumber(until)) =>
          TLAValueSet((from to until).view.map(TLAValueNumber).toSet)
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.DivSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          require(rhs != 0)
          TLAValueNumber(math.floorDiv(lhs, rhs))
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.PercentSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          require(rhs > 0)
          TLAValueNumber(math.floorMod(lhs, rhs))
      },

      BuiltinModules.Integers.memberAlpha("Int") -> { _ => throw Unsupported() },
      BuiltinModules.Integers.memberSym(TLASymbol.NegationSymbol) -> {
        case List(TLAValueNumber(num)) => TLAValueNumber(-num)
      },

      BuiltinModules.Reals.memberAlpha("Real") -> { _ => throw Unsupported() },
      BuiltinModules.Reals.memberSym(TLASymbol.SlashSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Reals.memberAlpha("Infinity") -> { _ => throw Unsupported() },
    ).to(ById.mapFactory)

  final class Result[+V] private (private val values: LazyList[Try[V]]) {
    //assert(values.nonEmpty)
    override def toString: String = s"Result($values)"

    def assumeUnambiguousSuccess: V = values.head.get

    def outcomes: LazyList[Try[V]] = values

    private def transformErr(err: Throwable): Throwable = err match {
      case err: IllegalArgumentException => TypeError().initCause(err)
      case err: MatchError => TypeError().initCause(err)
      case err => err
    }

    private def transformTryErr[T](t: Try[T]): Try[T] = t match {
      case Failure(err) => Failure(transformErr(err))
      case s@Success(_) => s
    }

    def map[U](fn: V=>U): Result[U] =
      new Result(values.map(tryValue => transformTryErr(tryValue.map(fn))))


    def map[U](fn: PartialFunction[V,U]): Result[U] = map(fn.apply _)

    def flatMap[U](fn: V=>Result[U]): Result[U] =
      new Result(values.flatMap {
        case Failure(err) => Iterator.single(Failure(err))
        case Success(value) =>
          try {
            fn(value).values
          } catch {
            case NonFatal(err) =>
              Iterator.single(Failure(transformErr(err)))
          }
      })

    def flatMap[U](fn: PartialFunction[V,Result[U]]): Result[U] = flatMap(fn.apply _)

    def ensureNodeInfo(node: TLANode): Result[V] =
      new Result(values.map {
        case Failure(err) =>
          err match {
            case err: TypeError => Failure(err.ensureNodeInfo(node))
            case err: Unsupported => Failure(err.ensureNodeInfo(node))
            case err => Failure(err)
          }
        case success: Success[V] => success
      })
  }

  object Result {
    def apply[V](v: =>V): Result[V] = new Result(LazyList(Try(v)))

    def multiple[V](vs: Iterable[V]): Result[V] = {
      val vsLzy = vs.to(LazyList)
      if(vsLzy.nonEmpty) {
        new Result(vsLzy.map(Success(_)))
      } else {
        new Result(LazyList(Failure(TypeError())))
      }
    }
  }

  def interpretList[R](exprs: List[TLAExpression])(validator: PartialFunction[TLAValue,R])(implicit env: Map[ById[RefersTo.HasReferences],TLAValue]): Result[List[R]] = {
    def impl(exprs: List[TLAExpression], acc: List[R]): Result[List[R]] =
      exprs match {
        case Nil => Result(acc.reverse)
        case expr :: restExprs =>
          interpret(expr).flatMap { value =>
            val r = validator(value)
            impl(restExprs, r :: acc)
          }
      }

    impl(exprs, Nil)
  }

  def flattenResultView[R](it: Iterable[Result[R]]): Result[Vector[R]] =
    it.foldLeft(Result(Vector.empty[R])) { (acc, result) =>
      acc.flatMap { prefix =>
        result.map(elem => prefix :+ elem)
      }
    }

  def interpret(expr: TLAExpression)(implicit env: Map[ById[RefersTo.HasReferences],TLAValue]): Result[TLAValue] = {
    Result(())
      .flatMap { _ =>
        expr.narrowMatch {
          case TLAString(value) => Result(TLAValueString(value))
          case TLANumber(value, _) =>
            value match {
              case TLANumber.IntValue(value) => Result(TLAValueNumber(value.intValue))
              case _ => throw Unsupported().ensureHint(d"only int literals are supported") // TODO: support the other ones
            }
          case ident@TLAGeneralIdentifier(_, prefix) =>
            assert(prefix.isEmpty)
            env.get(ById(ident.refersTo)) match {
              case Some(value) =>
                Result(value)
              case None =>
                ident.refersTo match {
                  case TLAOperatorDefinition(_, args, body, _) =>
                    assert(args.isEmpty)
                    interpret(body)
                  case _ =>
                    builtinOperators.get(ById(ident.refersTo)) match {
                      case Some(operator) =>
                        Result(operator(Nil))
                      case None =>
                        throw Unsupported()
                          .ensureNodeInfo(ident)
                          .ensureHint(d"scoping error, check e.g your constant definitions")
                    }
                }
            }
          case TLADot(lhs, identifier) =>
            interpret(lhs).map {
              case TLAValueFunction(value) =>
                val idx = TLAValueString(identifier.id)
                require(value.contains(idx))
                value(idx)
            }
          case TLACrossProduct(operands) =>
            interpretList(operands) {
              case TLAValueSet(set) => set
            }.map { sets =>
              val tuples = sets.tail.foldLeft(sets.head.iterator.map(elem => Vector(elem))) { (tuples, set) =>
                tuples.flatMap { tuple =>
                  set.iterator.map(elem => tuple :+ elem)
                }
              }
              TLAValueSet(tuples.map(TLAValueTuple).toSet)
            }
          case opcall@TLAOperatorCall(_, _, arguments) =>
            opcall.refersTo match {
              // TLA+ LAMBDA and operator-like CONSTANT support
              case ref if env.contains(ById(ref)) =>
                env(ById(ref)).narrowMatch {
                  case TLAValueLambda(fn) =>
                    interpretList(arguments)(PartialFunction.fromFunction(identity)).map { arguments =>
                      fn.applyOrElse(arguments, { (arguments: List[TLAValue]) =>
                        throw TypeError()
                          .ensureValueInfo(TLAValueTuple(Vector.from(arguments)))
                          .ensureNodeInfo(opcall)
                      })
                    }
                }
              // 3 special cases implement short-circuiting boolean logic
              case ref if ref eq BuiltinModules.Intrinsics.memberSym(TLASymbol.LogicalAndSymbol) =>
                val List(lhs, rhs) = arguments
                interpret(lhs).flatMap {
                  case TLAValueBool(true) => interpret(rhs)
                  case TLAValueBool(false) => Result(TLAValueBool(false))
                }
              case ref if ref eq BuiltinModules.Intrinsics.memberSym(TLASymbol.LogicalOrSymbol) =>
                val List(lhs, rhs) = arguments
                interpret(lhs).flatMap {
                  case TLAValueBool(true) => Result(TLAValueBool(true))
                  case TLAValueBool(false) => interpret(rhs)
                }
              case ref if ref eq BuiltinModules.Intrinsics.memberSym(TLASymbol.ImpliesSymbol) =>
                val List(lhs, rhs) = arguments
                interpret(lhs).flatMap {
                  case TLAValueBool(true) => interpret(rhs)
                  case TLAValueBool(false) => Result(TLAValueBool(true))
                }
              case builtin: BuiltinModules.TLABuiltinOperator =>
                interpretList(arguments)(PartialFunction.fromFunction(identity)).map { arguments =>
                  builtinOperators(ById(builtin))(arguments)
                }
              case TLAOperatorDefinition(_, args, body, _) =>
                require(args.size == arguments.size)
                require(args.forall(_.variant.isInstanceOf[TLAOpDecl.NamedVariant]))
                interpretList(arguments)(PartialFunction.fromFunction(identity)).flatMap { argValues =>
                  interpret(body)(env = env ++ (args.iterator.map(ById(_)) zip argValues))
                }
            }
          case TLAIf(cond, tval, fval) =>
            interpret(cond).flatMap {
              case TLAValueBool(value) =>
                if (value) interpret(tval) else interpret(fval)
            }
          case TLALet(defs, body) =>
            def impl(defs: List[TLAUnit])(implicit env: Map[ById[RefersTo.HasReferences], TLAValue]): Result[TLAValue] =
              defs match {
                case Nil => interpret(body)
                case unit :: restUnits =>
                  unit.narrowMatch {
                    case defn@TLAOperatorDefinition(_, args, body, _) if args.isEmpty =>
                      interpret(body).flatMap { bodyVal =>
                        impl(restUnits)(env = env.updated(ById(defn), bodyVal))
                      }
                    case _: TLAOperatorDefinition =>
                      // for definitions with args, they will be called by TLAOperatorCall, and scoping is done already
                      impl(restUnits)
                  }
              }

            impl(defs)
          case TLACase(arms, other) =>
            def armEval(arms: List[TLACaseArm]): Result[TLAValue] =
              arms match {
                case Nil => other match {
                  case Some(value) => interpret(value)
                  case None => throw TypeError()
                }
                case TLACaseArm(cond, result) :: otherArms =>
                  interpret(cond).flatMap {
                    case TLAValueBool(value) =>
                      if (value) {
                        interpret(result)
                      } else {
                        armEval(otherArms)
                      }
                  }
              }

            armEval(arms)
          case TLAFunction(args, body) =>
            interpretList(args.map(_.set)) {
              case TLAValueSet(set) => set
            }.flatMap { argSets =>
              def impl(args: List[TLAQuantifierBound], argSets: List[Set[TLAValue]], acc: Vector[TLAValue])(implicit env: Map[ById[RefersTo.HasReferences], TLAValue]): Result[View[(TLAValue, TLAValue)]] =
                (args, argSets) match {
                  case (Nil, Nil) =>
                    interpret(body)
                      .map { bodyVal =>
                        if(acc.size == 1) {
                          View(acc.head -> bodyVal)
                        } else {
                          View(TLAValueTuple(acc) -> bodyVal)
                        }
                      }
                  case (TLAQuantifierBound(tpe, ids, _) :: restArgs, argSet :: restArgSets) =>
                    tpe match {
                      case TLAQuantifierBound.IdsType =>
                        val List(id) = ids
                        flattenResultView(argSet.view.map { v =>
                          impl(restArgs, restArgSets, acc :+ v)(env = env.updated(ById(id), v))
                        }).map(_.view.flatten)
                      case TLAQuantifierBound.TupleType =>
                        flattenResultView(argSet.view.map(valueFn {
                          case v@TLAValueTuple(elems) =>
                            require(elems.size == ids.size)
                            impl(restArgs, restArgSets, acc :+ v)(env = env ++ (ids.view.map(ById(_)) zip elems))
                        })).map(_.view.flatten)
                    }
                  case (badNodes, _) =>
                    val err = Unsupported()
                    badNodes.headOption
                      .foreach { badNode =>
                        err.ensureNodeInfo(badNode)
                      }
                    throw err
                }

              if(argSets.exists(_.isEmpty)) {
                // short-circuit if one of the sets is empty, for parity with Go version
                Result(TLAValueFunction(Map.empty))
              } else {
                impl(args, argSets, Vector.empty).map { fnData =>
                  TLAValueFunction(fnData.toMap)
                }
              }
            }
          case TLAFunctionCall(function, params) =>
            (params match {
              case List(singleParam) => interpret(singleParam)
              case params => interpretList(params)(PartialFunction.fromFunction(identity)).map { paramVals =>
                TLAValueTuple(paramVals.toVector)
              }
            }).flatMap { paramValue =>
              interpret(function).map {
                case TLAValueTuple(value) =>
                  paramValue.narrowMatch {
                    case TLAValueNumber(idx) if idx >= 1 && idx <= value.size => value(idx - 1)
                  }
                case TLAValueFunction(value) =>
                  require(value.contains(paramValue))
                  value(paramValue)
              }
            }
          case TLAFunctionSet(from, to) =>
            interpret(from).flatMap {
              case TLAValueSet(fromSet) =>
                interpret(to).map {
                  case TLAValueSet(toSet) =>
                    TLAValueSet {
                      val keyList = fromSet.toList
                      val valueList = toSet.toList
                      val valueSets = keyList.iterator.foldLeft(Iterator.single(Nil: List[TLAValue])) { (acc, _) =>
                        acc.flatMap(lst => valueList.iterator.map(v => v :: lst))
                      }
                      valueSets.map(valueSet => TLAValueFunction((keyList zip valueSet).toMap)).toSet
                    }: TLAValue
                }
            }
          case TLAFunctionSubstitution(source, substitutions) =>
            substitutions.foldLeft(interpret(source)) { (fnValue, sub) =>
              fnValue.flatMap { fnValue =>
                val TLAFunctionSubstitutionPair(anchor, keys, value) = sub

                def subKeys(keys: List[TLAFunctionSubstitutionKey], origValue: TLAValue): Result[TLAValue] =
                  keys match {
                    case Nil => interpret(value)(env = env.updated(ById(anchor), origValue))
                    case TLAFunctionSubstitutionKey(indices) :: restKeys =>
                      (indices match {
                        case List(index) => interpret(index)
                        case indices =>
                          interpretList(indices)(PartialFunction.fromFunction(identity))
                            .map(indexVals => TLAValueTuple(indexVals.toVector))
                      }).flatMap { indexValue =>
                        origValue.narrowMatch {
                          case TLAValueFunction(origFn) =>
                            require(origFn.contains(indexValue))
                            subKeys(restKeys, origFn(indexValue)).map { subKeysVal =>
                              TLAValueFunction(origFn.updated(indexValue, subKeysVal))
                            }
                        }
                      }
                  }

                subKeys(keys, fnValue)
              }
            }
          case at@TLAFunctionSubstitutionAt() => Result(env(ById(at.refersTo)))
          case expr@(TLAQuantifiedExistential(_, _) | TLAQuantifiedUniversal(_, _)) =>
            // merge universal and existential code paths, because they are so similar
            val (bounds, body) = expr.narrowMatch {
              case TLAQuantifiedUniversal(bounds, body) => (bounds, body)
              case TLAQuantifiedExistential(bounds, body) => (bounds, body)
            }

            interpretList(bounds.map(_.set)) {
              case TLAValueSet(set) => set // require all sets to be actual sets
            }.flatMap { boundValues =>

              // compute a configuration iterator of lists of set elements to consider, so that we don't end up evaluating _anything_ on any
              // set elements until we know we should evaluate the body at least once (i.e if one set is empty, this
              // view will also be empty)
              val configurations: View[List[TLAValue]] = locally {
                @tailrec
                def impl(boundValues: List[Set[TLAValue]], acc: View[List[TLAValue]]): View[List[TLAValue]] =
                  boundValues match {
                    case Nil => acc
                    case set :: restSets =>
                      impl(restSets, acc.flatMap(config => set.view.map(config :+ _)))
                  }

                if (boundValues.nonEmpty && boundValues.tail.nonEmpty) {
                  impl(boundValues.tail, boundValues.head.view.map(List(_)))
                } else if (boundValues.nonEmpty) {
                  boundValues.head.view.map(List(_))
                } else {
                  !!!
                }
              }

              // a function that slots in at the decision point, choosing exists or forall aggregation
              val fn: Vector[Boolean] => Boolean = expr.narrowMatch {
                case TLAQuantifiedUniversal(_, _) => _.forall(identity)
                case TLAQuantifiedExistential(_, _) => _.exists(identity)
              }

              flattenResultView(configurations.map { args =>
                val bindings = (bounds.iterator zip args).flatMap {
                  case (TLAQuantifierBound(tpe, ids, _), assignment) =>
                    tpe match {
                      case TLAQuantifierBound.IdsType => Some(ById(ids.head) -> assignment)
                      case TLAQuantifierBound.TupleType =>
                        assignment.narrowMatch {
                          case TLAValueTuple(elems) =>
                            require(elems.size == ids.size)
                            ids.iterator.map(ById(_)) zip elems
                        }
                    }
                }
                interpret(body)(env = env ++ bindings).map {
                  case TLAValueBool(truth) => truth
                }
              }).map(truths => TLAValueBool(fn(truths)))
            }
          case TLASetConstructor(contents) =>
            interpretList(contents)(PartialFunction.fromFunction(identity)).map { contents =>
              TLAValueSet(contents.toSet)
            }
          case TLASetRefinement(TLAQuantifierBound(tpe, ids, set), when) =>
            interpret(set).flatMap {
              case TLAValueSet(setValue) =>
                tpe match {
                  case TLAQuantifierBound.IdsType =>
                    val List(id) = ids
                    val memberOpts = setValue.view.map { v =>
                      interpret(when)(env = env.updated(ById(id), v)).map {
                        case TLAValueBool(shouldKeep) => if (shouldKeep) Some(v) else None
                      }
                    }
                    flattenResultView(memberOpts).map { memberOpts =>
                      TLAValueSet(memberOpts.flatten.toSet): TLAValue
                    }
                  case TLAQuantifierBound.TupleType =>
                    val memberOpts = setValue.view.map {
                      case v@TLAValueTuple(elems) =>
                        require(elems.size == ids.size)
                        interpret(when)(env = env ++ (ids.view.map(ById(_)) zip elems)).map {
                          case TLAValueBool(shouldKeep) => if (shouldKeep) Some(v) else None
                        }
                      case _ => require(false); !!!
                    }
                    flattenResultView(memberOpts).map { memberOpts =>
                      TLAValueSet(memberOpts.flatten.toSet): TLAValue
                    }
                }
            }
          case TLASetComprehension(body, bounds) =>
            interpretList(bounds.map(_.set)) {
              case TLAValueSet(set) => set // require all sets are actual sets
            }.flatMap { boundValues =>
              def impl(bounds: List[TLAQuantifierBound], boundValues: List[Set[TLAValue]])(implicit env: Map[ById[RefersTo.HasReferences], TLAValue]): Result[View[TLAValue]] =
                (bounds, boundValues) match {
                  case (Nil, Nil) => interpret(body).map(View(_))
                  case (TLAQuantifierBound(tpe, ids, _) :: restBounds, setValue :: restSetValues) =>
                    tpe match {
                      case TLAQuantifierBound.IdsType =>
                        val List(id) = ids
                        flattenResultView(setValue.view.map { v =>
                          impl(restBounds, restSetValues)(env = env.updated(ById(id), v))
                        }).map(_.view.flatten)
                      case TLAQuantifierBound.TupleType =>
                        flattenResultView(setValue.view.map {
                          case TLAValueTuple(elems) =>
                            require(ids.size == elems.size)
                            impl(restBounds, restSetValues)(env = env ++ (ids.view.map(ById(_)) zip elems))
                          case _ => require(false); !!!
                        }).map(_.view.flatten)
                    }
                  case _ => !!!
                }

              impl(bounds, boundValues).map { members =>
                TLAValueSet(members.toSet)
              }
            }
          case TLATuple(elements) =>
            interpretList(elements)(PartialFunction.fromFunction(identity))
              .map(elements => TLAValueTuple(elements.toVector))
          case TLARecordConstructor(fields) =>
            flattenResultView(fields.view.map {
              case TLARecordConstructorField(name, value) =>
                interpret(value).map(TLAValueString(name.id) -> _)
            }).map(pairs => TLAValueFunction(pairs.toMap))
          case TLARecordSet(fields) =>
            def impl(fields: List[(String, TLAValue)], acc: Map[TLAValue, TLAValue]): Iterator[TLAValue] =
              fields match {
                case Nil => Iterator.single(TLAValueFunction(acc))
                case (name, value) :: restFields =>
                  value.narrowMatch {
                    case TLAValueSet(set) =>
                      set.iterator.flatMap { v =>
                        impl(restFields, acc.updated(TLAValueString(name), v))
                      }
                  }
              }

            flattenResultView(fields.view.map {
              case TLARecordSetField(name, set) =>
                interpret(set).map {
                  case setVal: TLAValueSet => name.id -> setVal
                }
            }).map { pairs =>
              TLAValueSet(impl(pairs.toList, Map.empty).toSet)
            }
          case TLAQuantifiedChoose(TLAQuantifierBound(tpe, ids, set), body) =>
            interpret(set).flatMap {
              case TLAValueSet(setValue) =>
                val validElements: View[Result[Option[TLAValue]]] = setValue.view.map { v =>
                  tpe match {
                    case TLAQuantifierBound.IdsType =>
                      val List(id) = ids
                      interpret(body)(env = env.updated(ById(id), v)).map {
                        case TLAValueBool(shouldInclude) => if(shouldInclude) Some(v) else None
                      }
                    case TLAQuantifierBound.TupleType =>
                      val TLAValueTuple(elems) = v
                      require(elems.size == ids.size)
                      interpret(body)(env = env ++ (ids.view.map(ById(_)) zip elems)).map {
                        case TLAValueBool(shouldInclude) => if(shouldInclude) Some(v) else None
                      }
                  }
                }
                flattenResultView(validElements).flatMap { candidateOpts =>
                  Result.multiple(candidateOpts.flatten)
                }
            }
        }
      }
      .ensureNodeInfo(expr)
  }
}
