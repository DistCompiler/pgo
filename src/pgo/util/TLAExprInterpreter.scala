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
import java.io.OutputStream
import pgo.model.PGoError
import java.nio.ByteBuffer
import scala.collection.mutable
import java.nio.charset.StandardCharsets
import pgo.model.tla.TLAQuantifierBound.IdsType
import pgo.model.tla.TLAQuantifierBound.TupleType
import java.io.Closeable
import os.write

object TLAExprInterpreter {
  private def mkExceptionDesc(
      reason: Description,
      badValue: Option[TLAValue],
      badNode: Option[TLANode]
  ): Description =
    d"evaluation error ($reason)${badValue match {
        case None => d""
        case Some(badValue) =>
          d", due to value ${badValue.describe}"
      }}${badNode match {
        case None => d""
        case Some(badNode) =>
          d" at ${badNode.sourceLocation.longDescription}".ensureLineBreakBefore.indented
      }}"

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
        reason =
          d"operation not supported by current configuration ${hint.map(h => d"[$h]").getOrElse(d"")}",
        badValue = None,
        badNode = badNode
      )
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

    def asTLCBinFmt: geny.Writable =
      val self = this
      new geny.Writable:
        final def writeBytesTo(out: OutputStream): Unit =
          object buffer extends Closeable:
            private val buf = ByteBuffer.allocate(4096)
            private def writeBuf(): Unit =
              out.write(buf.array(), 0, buf.position())
              buf.clear()

            def capacity: Int = buf.capacity()

            def flush(): Unit =
              if buf.position() > 0
              then writeBuf()

            def apply(size: Int): ByteBuffer =
              if buf.remaining() < size
              then writeBuf()
              buf

            def close(): Unit =
              flush()

          val stringUniqTable = mutable.HashMap[String, Int]()

          def writeByte(byte: Byte): Unit =
            val buf = buffer(1)
            buf.put(byte)

          def writeArray(arr: Array[Byte]): Unit =
            if arr.length <= buffer.capacity
            then
              val buf = buffer(arr.length)
              buf.put(arr)
            else
              buffer.flush()
              out.write(arr)

          def writeShort(short: Short): Unit =
            val buf = buffer(2)
            buf.asShortBuffer().put(short)
            buf.position(buf.position() + 2)

          def writeInt(int: Int): Unit =
            val buf = buffer(4)
            buf.asIntBuffer().put(int)
            buf.position(buf.position() + 4)

          def writeNat(x: Int): Unit =
            if x > 0x7fff
            then writeInt(-x)
            else writeShort(x.toShort)

          def impl(value: TLAValue): Unit =
            value match
              case TLAValueModel(name) =>
                throw RuntimeException("cannot serialize TLA+ model value")
              case TLAValueBool(value) =>
                writeByte(0) // BOOLEANVALUE
                writeByte(if value then 1 else 0)
              case TLAValueNumber(value) =>
                writeByte(1) // INTVALUE
                writeInt(value)
              case TLAValueString(value) =>
                writeByte(3) // STRINGVALUE
                val tok =
                  stringUniqTable.getOrElseUpdate(value, stringUniqTable.size)
                writeInt(tok)
                writeInt(
                  -1
                ) // == tok if the string "is a variable"... probably not relevant

                // TLC below a certain version only handles ASCII, but should handle UTF-8 in future.
                val strBytes = value.getBytes(StandardCharsets.UTF_8)
                writeInt(strBytes.length)
                writeArray(strBytes)
              case TLAValueSet(value) =>
                writeByte(5) // SETENUMVALUE
                writeInt(
                  -value.size
                ) // negative value means not normalized. We can't guarantee same sort order as TLC
                value.foreach(impl)
              case TLAValueTuple(value) =>
                writeByte(7) // TUPLEVALUE
                writeNat(value.length)
                value.foreach(impl)
              case TLAValueFunction(value) =>
                // Note: "record" is also an option here, but we don't have an explicit representation for it.
                //       I assume TLC will forgive me if I encode something that could have been a "record" as this more
                //       general construct.
                writeByte(9) // FCNRCDVALUE
                writeNat(value.size)
                writeByte(
                  2
                ) // 0 if a compressed interval (we don't support this), 1 if normalized (no, requires sorting), 2 if neither
                value.foreach: (k, v) =>
                  impl(k)
                  impl(v)
              case TLAValueLambda(fn) =>
                throw RuntimeException("cannot serialize TLA+ lambda value")

          try
            impl(self)
          finally
            buffer.close()
        end writeBytesTo
    end asTLCBinFmt
  }

  object TLAValue {
    def parseFromString(str: String): TLAValue = {
      val expr = TLAParser.readExpression(
        new SourceLocation.UnderlyingString(str),
        str,
        // Integers needed for prefix `-`, and TLC needed for `:>` and `@@`
        definitions =
          BuiltinModules.Integers.members ::: BuiltinModules.TLC.members
      )
      interpret(expr)(using Map.empty)
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
      d"{${value.view
          .map(_.describe)
          .separateBy(d", ")}}"
  }
  final case class TLAValueTuple(value: Vector[TLAValue]) extends TLAValue {
    override def describe: Description =
      d"<<${value.view
          .map(_.describe)
          .separateBy(d", ")}>>"
  }
  final case class TLAValueFunction(value: Map[TLAValue, TLAValue])
      extends TLAValue {
    override def describe: Description = {
      if (value.isEmpty) {
        "[x \\in {} |-> x]".description
      } else {
        d"(${value.view
            .map { case (key, value) =>
              d"(${key.describe}) :> (${value.describe})".indented
            }
            .separateBy(d" @@ ")})"
      }
    }
  }

  final case class TLAValueLambda(fn: PartialFunction[List[TLAValue], TLAValue])
      extends TLAValue {
    override def describe: Description =
      d"LAMBDA ${String.format("%x", System.identityHashCode(fn))}"
  }

  private[pgo] def valueFn[T](fn: PartialFunction[TLAValue, T]): TLAValue => T =
    fn.orElse { (badValue: TLAValue) =>
      throw TypeError().ensureValueInfo(badValue)
    }

  private[pgo] final implicit class TLAValueOps(value: TLAValue) {
    def narrowMatch[T](fn: PartialFunction[TLAValue, T]): T =
      fn.applyOrElse(
        value,
        { (badValue: TLAValue) =>
          throw TypeError().ensureValueInfo(badValue)
        }
      )
  }

  extension [N <: TLANode](node: N)
    private[pgo] final def narrowMatch[T](fn: PartialFunction[N, T]): T =
      try
        fn.applyOrElse(
          node,
          { (badNode: TLANode) =>
            throw Unsupported().ensureNodeInfo(badNode)
          }
        )
      catch
        case err: TypeError => throw err.ensureNodeInfo(node)
        case err: IllegalArgumentException =>
          throw TypeError().ensureNodeInfo(node).initCause(err)
        case err: MatchError =>
          throw TypeError().ensureNodeInfo(node).initCause(err)

  lazy val builtinOperators
      : Map[ById[DefinitionOne], PartialFunction[List[TLAValue], TLAValue]] =
    View[(DefinitionOne, PartialFunction[List[TLAValue], TLAValue])](
      BuiltinModules.Intrinsics.memberSym(TLASymbol.LogicalAndSymbol) -> {
        case List(TLAValueBool(lhs), TLAValueBool(rhs)) =>
          TLAValueBool(lhs && rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.LogicalOrSymbol) -> {
        case List(TLAValueBool(lhs), TLAValueBool(rhs)) =>
          TLAValueBool(lhs || rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.LogicalNotSymbol) -> {
        case List(TLAValueBool(op)) => TLAValueBool(!op)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.ImpliesSymbol) -> {
        case List(TLAValueBool(lhs), TLAValueBool(rhs)) =>
          TLAValueBool(!lhs || rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.EquivSymbol) -> {
        case List(TLAValueBool(lhs), TLAValueBool(rhs)) =>
          TLAValueBool(lhs == rhs)
      },
      BuiltinModules.Intrinsics.memberAlpha("TRUE") -> { case Nil =>
        TLAValueBool(true)
      },
      BuiltinModules.Intrinsics.memberAlpha("FALSE") -> { case Nil =>
        TLAValueBool(false)
      },
      BuiltinModules.Intrinsics.memberAlpha("BOOLEAN") -> { case Nil =>
        TLAValueSet(Set(TLAValueBool(true), TLAValueBool(false)))
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
        case List(TLAValueSet(lhs), TLAValueSet(rhs)) =>
          TLAValueBool(lhs.subsetOf(rhs))
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.BackslashSymbol) -> {
        case List(TLAValueSet(lhs), TLAValueSet(rhs)) =>
          TLAValueSet(lhs.diff(rhs))
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.PrefixUnionSymbol) -> {
        case List(TLAValueSet(set)) =>
          TLAValueSet(set.subsets().map(TLAValueSet.apply).toSet)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.PrefixUnionSymbol) -> {
        case List(TLAValueSet(set)) =>
          TLAValueSet(
            set.view
              .flatMap(valueFn { case TLAValueSet(memberSet) =>
                memberSet
              })
              .toSet
          )
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.DomainSymbol) -> {
        case List(TLAValueFunction(fn)) => TLAValueSet(fn.keySet)
      },
      BuiltinModules.Intrinsics.memberAlpha("STRING") -> { case Nil =>
        throw Unsupported()
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.PrimeSymbol) -> { _ =>
        throw Unsupported()
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.EnabledSymbol) -> { _ =>
        throw Unsupported()
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.UnchangedSymbol) -> { _ =>
        throw Unsupported()
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.CDotSymbol) -> { _ =>
        throw Unsupported()
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.TLAlwaysSymbol) -> { _ =>
        throw Unsupported()
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.TLEventuallySymbol) -> {
        _ => throw Unsupported()
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.SequencingSymbol) -> { _ =>
        throw Unsupported()
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.PlusArrowSymbol) -> { _ =>
        throw Unsupported()
      },
      BuiltinModules.TLC.memberAlpha("Print") -> { case List(_, _) =>
        throw Unsupported()
      },
      BuiltinModules.TLC.memberAlpha("PrintT") -> { case List(_) =>
        throw Unsupported()
      },
      BuiltinModules.TLC.memberAlpha("Assert") -> {
        case List(TLAValueBool(cond), out) =>
          require(cond, out.toString)
          TLAValueBool(true)
      },
      BuiltinModules.TLC.memberAlpha("JavaTime") -> { case Nil =>
        throw Unsupported()
      },
      BuiltinModules.TLC.memberSym(TLASymbol.ColonGreaterThanSymbol) -> {
        case List(lhs, rhs) => TLAValueFunction(Map(lhs -> rhs))
      },
      BuiltinModules.TLC.memberSym(TLASymbol.DoubleAtSignSymbol) -> {
        case List(TLAValueFunction(lhs), TLAValueFunction(rhs)) =>
          TLAValueFunction(lhs ++ rhs)
      },
      BuiltinModules.TLC.memberAlpha("Permutations") -> { _ =>
        throw Unsupported()
      },
      BuiltinModules.TLC.memberAlpha("SortSeq") -> { _ => throw Unsupported() },
      BuiltinModules.TLC.memberAlpha("ToString") -> {
        case List(value: TLAValue) =>
          TLAValueString(value.describe.linesIterator.mkString("\n"))
      },
      BuiltinModules.Sequences.memberAlpha("Seq") -> {
        case List(TLAValueSet(elems)) =>
          TLAValueSet(
            elems.toVector.permutations.map(TLAValueTuple.apply).toSet
          )
      },
      BuiltinModules.Sequences.memberAlpha("Len") -> {
        case List(TLAValueTuple(elems)) => TLAValueNumber(elems.size)
      },
      BuiltinModules.Sequences.memberSym(TLASymbol.OSymbol) -> {
        case List(TLAValueTuple(lhs), TLAValueTuple(rhs)) =>
          TLAValueTuple(lhs ++ rhs)
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
        case List(TLAValueTuple(_), TLAValueNumber(from), TLAValueNumber(to))
            if from > to =>
          TLAValueTuple(Vector.empty)
        case List(
              TLAValueTuple(elems),
              TLAValueNumber(from1),
              TLAValueNumber(to1)
            ) =>
          val from = from1 - 1
          val to = to1 - 1
          require(from >= 0 && to >= 0 && from < elems.size && to < elems.size)
          TLAValueTuple(elems.slice(from, to + 1))
      },
      BuiltinModules.Sequences.memberAlpha("SelectSeq") -> { _ =>
        throw Unsupported()
      },
      BuiltinModules.FiniteSets.memberAlpha("IsFiniteSet") -> {
        case List(TLAValueSet(_)) => TLAValueBool(true)
      },
      BuiltinModules.FiniteSets.memberAlpha("Cardinality") -> {
        case List(TLAValueSet(set)) => TLAValueNumber(set.size)
      },
      BuiltinModules.Bags.memberAlpha("IsABag") -> { case List(_) =>
        throw Unsupported()
      },
      BuiltinModules.Bags.memberAlpha("BagToSet") -> { case List(_) =>
        throw Unsupported()
      },
      BuiltinModules.Bags.memberAlpha("SetToBag") -> { case List(_) =>
        throw Unsupported()
      },
      BuiltinModules.Bags.memberAlpha("BagIn") -> { case List(_, _) =>
        throw Unsupported()
      },
      BuiltinModules.Bags.memberAlpha("EmptyBag") -> { case Nil =>
        throw Unsupported()
      },
      BuiltinModules.Bags.memberAlpha("CopiesIn") -> { case List(_, _) =>
        throw Unsupported()
      },
      BuiltinModules.Bags.memberSym(TLASymbol.OPlusSymbol) -> { _ =>
        throw Unsupported()
      },
      BuiltinModules.Bags.memberSym(TLASymbol.OMinusSymbol) -> { _ =>
        throw Unsupported()
      },
      BuiltinModules.Bags.memberAlpha("BagUnion") -> { case List(_) =>
        throw Unsupported()
      },
      BuiltinModules.Bags.memberSym(TLASymbol.SquareSupersetOrEqualSymbol) -> {
        _ => throw Unsupported()
      },
      BuiltinModules.Bags.memberAlpha("SubBag") -> { case List(_) =>
        throw Unsupported()
      },
      BuiltinModules.Bags.memberAlpha("BagOfAll") -> { case List(_, _) =>
        throw Unsupported()
      },
      BuiltinModules.Bags.memberAlpha("BagCardinality") -> { case List(_) =>
        throw Unsupported()
      },
      BuiltinModules.Peano.memberAlpha("PeanoAxioms") -> { case List(_, _, _) =>
        throw Unsupported()
      },
      BuiltinModules.Peano.memberAlpha("Succ") -> { case Nil =>
        throw Unsupported()
      },
      BuiltinModules.Peano.memberAlpha("Nat") -> { case Nil =>
        throw Unsupported()
      },
      BuiltinModules.Peano.memberAlpha("Zero") -> { case Nil =>
        TLAValueNumber(0)
      },
      BuiltinModules.ProtoReals.memberAlpha("IsModelOfReals") -> {
        case List(_, _, _, _) => throw Unsupported()
      },
      BuiltinModules.ProtoReals.memberAlpha("RM") -> { case Nil =>
        throw Unsupported()
      },
      BuiltinModules.ProtoReals.memberAlpha("Real") -> { case Nil =>
        throw Unsupported()
      },
      BuiltinModules.ProtoReals.memberAlpha("Infinity") -> { case Nil =>
        throw Unsupported()
      },
      BuiltinModules.ProtoReals.memberAlpha("MinusInfinity") -> { case Nil =>
        throw Unsupported()
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.PlusSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          TLAValueNumber(math.addExact(lhs, rhs))
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.AsteriskSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          TLAValueNumber(math.multiplyExact(lhs, rhs))
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.LessThanOrEqualSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          TLAValueBool(lhs <= rhs)
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.MinusSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          TLAValueNumber(math.subtractExact(lhs, rhs))
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.SlashSymbol) -> {
        case List(_, _) => throw Unsupported()
      },
      BuiltinModules.ProtoReals.memberAlpha("Int") -> { case Nil =>
        throw Unsupported()
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.SuperscriptSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          // don't silently truncate overflows; fail with error
          val result = math.pow(lhs, rhs)
          require(result <= Int.MaxValue && result >= Int.MinValue)
          TLAValueNumber(result.toInt)
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.GreaterThanOrEqualSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          TLAValueBool(lhs >= rhs)
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.LessThanSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          TLAValueBool(lhs < rhs)
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.GreaterThanSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          TLAValueBool(lhs > rhs)
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.DotDotSymbol) -> {
        case List(TLAValueNumber(from), TLAValueNumber(until)) =>
          TLAValueSet((from to until).view.map(TLAValueNumber.apply).toSet)
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
      BuiltinModules.Integers.memberAlpha("Int") -> { _ =>
        throw Unsupported()
      },
      BuiltinModules.Integers.memberSym(TLASymbol.NegationSymbol) -> {
        case List(TLAValueNumber(num)) => TLAValueNumber(-num)
      },
      BuiltinModules.Reals.memberAlpha("Real") -> { _ => throw Unsupported() },
      BuiltinModules.Reals.memberSym(TLASymbol.SlashSymbol) -> { _ =>
        throw Unsupported()
      },
      BuiltinModules.Reals.memberAlpha("Infinity") -> { _ =>
        throw Unsupported()
      }
    ).to(ById.mapFactory)

  final class Result[+V] private (private val value: Try[V]) extends AnyVal {
    override def toString: String = s"Result($value)"

    def assumeSuccess: V = value.get

    def outcomes: LazyList[Try[V]] = LazyList(value)

    private def transformErr(err: Throwable): Throwable = err match {
      case err: IllegalArgumentException => TypeError().initCause(err)
      case err: MatchError               => TypeError().initCause(err)
      case err                           => err
    }

    private def transformTryErr[T](t: Try[T]): Try[T] = t match {
      case Failure(err)   => Failure(transformErr(err))
      case s @ Success(_) => s
    }

    def map[U](fn: V => U): Result[U] =
      new Result(transformTryErr(value.map(fn)))

    def map[U](fn: PartialFunction[V, U]): Result[U] = map(fn.apply)

    def flatMap[U](fn: V => Result[U]): Result[U] =
      new Result(value match {
        case Failure(err) => Failure(err)
        case Success(value) =>
          try {
            fn(value).value
          } catch {
            case NonFatal(err) =>
              Failure(transformErr(err))
          }
      })

    def flatMap[U](fn: PartialFunction[V, Result[U]]): Result[U] = flatMap(
      fn.apply
    )

    def ensureNodeInfo(node: TLANode): Result[V] =
      new Result(value match {
        case Failure(err) =>
          err match {
            case err: TypeError   => Failure(err.ensureNodeInfo(node))
            case err: Unsupported => Failure(err.ensureNodeInfo(node))
            case err              => Failure(err)
          }
        case success: Success[V] => success
      })
  }

  object Result {
    def apply[V](v: => V): Result[V] = new Result(Try(v))
  }

  type Env = Map[ById[RefersTo.HasReferences], TLAValue]

  private def allEnvChoices(
      bounds: List[TLAQuantifierBound],
      forceAll: Boolean = false
  )(using
      env: Env
  ): View[Env] =
    var hadEmpty = false
    val boundValues =
      bounds.view
        .map(_.set)
        .map(interpret)
        .map(_.narrowMatch { case TLAValueSet(set) => set })
        .tapEach(set => hadEmpty |= set.isEmpty)
        .takeWhile(_.nonEmpty || forceAll)
        .toList

    // short-circuit on empty
    if hadEmpty then return View.empty

    val assignmentGroups =
      bounds.view
        .flatMap:
          case TLAQuantifierBound(TLAQuantifierBound.IdsType, ids, set) =>
            val setValue = interpret(set).narrowMatch { case TLAValueSet(set) =>
              set
            }
            ids.view.map(id => ById(id) -> setValue)
          case TLAQuantifierBound(TLAQuantifierBound.TupleType, ids, set) =>
            val setValue = interpret(set).narrowMatch { case TLAValueSet(set) =>
              set
            }
            ids.view.zipWithIndex
              .map: (id, idx) =>
                ById(id) -> setValue.map: tpl =>
                  tpl.narrowMatch:
                    case TLAValueTuple(tpl) =>
                      require(tpl.size == ids.size)
                      tpl(idx)
        .toMap

    assignmentGroups
      .foldLeft(
        None: Option[View[Map[ById[RefersTo.HasReferences], TLAValue]]]
      ):
        case (None, (id, set)) =>
          Some(set.view.map(v => Map(id -> v)))
        case (Some(acc), (id, set)) =>
          Some(set.view.flatMap(v => acc.map(_.updated(id, v))))
      .get

  def interpret(expr: TLAExpression)(using
      env: Env
  ): TLAValue = {
    expr.narrowMatch:
      case TLAString(value) => TLAValueString(value)
      case TLANumber(value, _) =>
        value match {
          case TLANumber.IntValue(value) =>
            TLAValueNumber(value.intValue)
          case _ =>
            throw Unsupported().ensureHint(
              d"only int literals are supported"
            ) // TODO: support the other ones
        }
      case ident @ TLAGeneralIdentifier(_, prefix) =>
        assert(prefix.isEmpty)
        env.get(ById(ident.refersTo)) match {
          case Some(value) =>
            value
          case None =>
            ident.refersTo match {
              case TLAOperatorDefinition(_, args, body, _) =>
                assert(args.isEmpty)
                interpret(body)
              case _ =>
                builtinOperators.get(ById(ident.refersTo)) match {
                  case Some(operator) =>
                    operator(Nil)
                  case None =>
                    throw Unsupported()
                      .ensureNodeInfo(ident)
                      .ensureHint(
                        d"scoping error, check e.g your constant definitions"
                      )
                }
            }
        }
      case TLADot(lhs, identifier) =>
        interpret(lhs).narrowMatch { case TLAValueFunction(value) =>
          val idx = TLAValueString(identifier.id)
          require(value.contains(idx))
          value(idx)
        }
      case TLACrossProduct(operands) =>
        operands.view
          .map(interpret)
          .map(_.narrowMatch { case TLAValueSet(set) => set })
          .foldLeft(None: Option[TLAValueSet]):
            case (None, set) =>
              Some(TLAValueSet(set.map(elem => TLAValueTuple(Vector(elem)))))
            case (Some(TLAValueSet(lhsSet)), rhsSet) =>
              Some:
                TLAValueSet:
                  lhsSet.flatMap:
                    case TLAValueTuple(lhsElems) =>
                      rhsSet.map(rhsElem => TLAValueTuple(lhsElems :+ rhsElem))
                    case _ => !!!
          .get
      case opcall @ TLAOperatorCall(_, _, arguments) =>
        opcall.refersTo match {
          // TLA+ LAMBDA and operator-like CONSTANT support
          case ref if env.contains(ById(ref)) =>
            env(ById(ref)).narrowMatch { case TLAValueLambda(fn) =>
              fn.applyOrElse(
                arguments.map(interpret),
                { (arguments: List[TLAValue]) =>
                  throw TypeError()
                    .ensureValueInfo(
                      TLAValueTuple(Vector.from(arguments))
                    )
                    .ensureNodeInfo(opcall)
                }
              )
            }
          // 3 special cases implement short-circuiting boolean logic
          case ref
              if ref eq BuiltinModules.Intrinsics.memberSym(
                TLASymbol.LogicalAndSymbol
              ) =>
            val List(lhs, rhs) = arguments
            interpret(lhs).narrowMatch {
              case TLAValueBool(true)  => interpret(rhs)
              case TLAValueBool(false) => TLAValueBool(false)
            }
          case ref
              if ref eq BuiltinModules.Intrinsics.memberSym(
                TLASymbol.LogicalOrSymbol
              ) =>
            val List(lhs, rhs) = arguments
            interpret(lhs).narrowMatch {
              case TLAValueBool(true)  => TLAValueBool(true)
              case TLAValueBool(false) => interpret(rhs)
            }
          case ref
              if ref eq BuiltinModules.Intrinsics.memberSym(
                TLASymbol.ImpliesSymbol
              ) =>
            val List(lhs, rhs) = arguments
            interpret(lhs).narrowMatch {
              case TLAValueBool(true)  => interpret(rhs)
              case TLAValueBool(false) => TLAValueBool(true)
            }
          case builtin: BuiltinModules.TLABuiltinOperator =>
            builtinOperators(ById(builtin))(arguments.map(interpret))
          case TLAOperatorDefinition(_, args, body, _) =>
            require(args.size == arguments.size)
            require(
              args.forall(_.variant.isInstanceOf[TLAOpDecl.NamedVariant])
            )
            interpret(body)(using
              env ++ (args.view.map(ById(_)) `zip` arguments.view.map(
                interpret
              ))
            )
        }
      case TLAIf(cond, tval, fval) =>
        interpret(cond).narrowMatch { case TLAValueBool(value) =>
          if (value) interpret(tval) else interpret(fval)
        }
      case TLALet(defs, body) =>
        def impl(defs: List[TLAUnit])(implicit
            env: Map[ById[RefersTo.HasReferences], TLAValue]
        ): TLAValue =
          defs match {
            case Nil => interpret(body)
            case unit :: restUnits =>
              unit.narrowMatch {
                case defn @ TLAOperatorDefinition(_, args, body, _)
                    if args.isEmpty =>
                  interpret(body).narrowMatch { bodyVal =>
                    impl(restUnits)(env = env.updated(ById(defn), bodyVal))
                  }
                case _: TLAOperatorDefinition =>
                  // for definitions with args, they will be called by TLAOperatorCall, and scoping is done already
                  impl(restUnits)
              }
          }

        impl(defs)
      case TLACase(arms, other) =>
        arms.view
          .map:
            case TLACaseArm(cond, result) =>
              interpret(cond).narrowMatch:
                case TLAValueBool(true) =>
                  Some(result)
                case TLAValueBool(false) =>
                  None
                case _ => throw TypeError().ensureNodeInfo(cond)
          .find(_.nonEmpty)
          .flatten
          .orElse(other)
          .map(interpret)
          .getOrElse(throw TypeError())
      case TLAFunction(args, body) =>
        val keySeq =
          args.view
            .flatMap:
              case TLAQuantifierBound(_, ids, _) => ids
            .toSeq
        val keyFn: (Env ?=> TLAValue) =
          if keySeq.size == 1
          then summon[Env](ById(keySeq.head))
          else
            TLAValueTuple:
              keySeq.view
                .map: id =>
                  summon[Env](ById(id))
                .toVector

        TLAValueFunction:
          allEnvChoices(args, forceAll = true)
            .map: env =>
              keyFn(using env) -> interpret(body)(using env)
            .toMap
      case TLAFunctionCall(function, params) =>
        val paramVal =
          params match
            case List(singleParam) => interpret(singleParam)
            case params => TLAValueTuple(params.view.map(interpret).toVector)

        interpret(function).narrowMatch {
          case TLAValueTuple(value) =>
            paramVal.narrowMatch {
              case TLAValueNumber(idx) if idx >= 1 && idx <= value.size =>
                value(idx - 1)
            }
          case TLAValueFunction(value) =>
            require(value.contains(paramVal))
            value(paramVal)
        }
      case TLAFunctionSet(from, to) =>
        val TLAValueSet(fromSet) = interpret(from): @unchecked
        val TLAValueSet(toSet) = interpret(to): @unchecked

        TLAValueSet {
          val keyList = fromSet.toList
          val valueList = toSet.toList
          val valueSets = keyList.iterator.foldLeft(
            Iterator.single(Nil: List[TLAValue])
          ) { (acc, _) =>
            acc.flatMap(lst => valueList.iterator.map(v => v :: lst))
          }
          valueSets
            .map(valueSet => TLAValueFunction((keyList zip valueSet).toMap))
            .toSet
        }
      case TLAFunctionSubstitution(source, substitutions) =>
        substitutions.foldLeft(interpret(source)) { (fnValue, sub) =>
          val TLAFunctionSubstitutionPair(anchor, keys, value) = sub

          def subKeys(
              keys: List[TLAFunctionSubstitutionKey],
              origValue: TLAValue
          ): TLAValue =
            keys match {
              case Nil =>
                interpret(value)(using env.updated(ById(anchor), origValue))
              case TLAFunctionSubstitutionKey(indices) :: restKeys =>
                val indexValue = indices match
                  case List(index) => interpret(index)
                  case indices =>
                    TLAValueTuple(indices.view.map(interpret).toVector)

                origValue.narrowMatch { case TLAValueFunction(origFn) =>
                  require(origFn.contains(indexValue))
                  val subValue = subKeys(restKeys, origFn(indexValue))
                  TLAValueFunction(origFn.updated(indexValue, subValue))
                }
            }

          subKeys(keys, fnValue)
        }
      case at @ TLAFunctionSubstitutionAt() =>
        env(ById(at.refersTo))
      case expr @ (TLAQuantifiedExistential(_, _) |
          TLAQuantifiedUniversal(_, _)) =>
        // merge universal and existential code paths, because they are so similar
        type CombineFn = View[Boolean] => Boolean
        val (bounds, body, combineFn) = expr.narrowMatch {
          case TLAQuantifiedUniversal(bounds, body) =>
            (bounds, body, (_.forall(identity)): CombineFn)
          case TLAQuantifiedExistential(bounds, body) =>
            (bounds, body, (_.exists(identity)): CombineFn)
        }

        val bools =
          allEnvChoices(bounds, forceAll = true)
            .map(interpret(body)(using _))
            .map(_.narrowMatch { case TLAValueBool(value) => value })

        TLAValueBool(combineFn(bools))
      case TLASetConstructor(contents) =>
        TLAValueSet(contents.view.map(interpret).toSet)
      case TLASetRefinement(TLAQuantifierBound(tpe, ids, set), when) =>
        val TLAValueSet(setValue) = interpret(set): @unchecked

        TLAValueSet:
          setValue
            .filter: elem =>
              tpe match
                case TLAQuantifierBound.IdsType =>
                  val List(id) = ids: @unchecked
                  interpret(when)(using env.updated(ById(id), elem))
                    .narrowMatch:
                      case TLAValueBool(value) => value
                case TLAQuantifierBound.TupleType =>
                  elem.narrowMatch:
                    case TLAValueTuple(elems) if elems.size == ids.size =>
                      interpret(when)(using
                        env ++ (ids.view.map(ById(_)) `zip` elems)
                      ).narrowMatch:
                        case TLAValueBool(value) => value
      case TLASetComprehension(body, bounds) =>
        val envs = allEnvChoices(bounds)
        TLAValueSet(envs.map(interpret(body)(using _)).toSet)
      case TLATuple(elements) =>
        TLAValueTuple(elements.view.map(interpret).toVector)
      case TLARecordConstructor(fields) =>
        TLAValueFunction:
          fields.view
            .map:
              case TLARecordConstructorField(name, value) =>
                TLAValueString(name.id) -> interpret(value)
            .toMap
      case TLARecordSet(fields) =>
        TLAValueSet:
          fields
            .foldLeft(None: Option[Set[Map[TLAValue, TLAValue]]]):
              case (None, TLARecordSetField(name, set)) =>
                interpret(set).narrowMatch:
                  case TLAValueSet(set) =>
                    Some(Set(set.view.map(TLAValueString(name.id) -> _).toMap))
              case (Some(acc), TLARecordSetField(name, set)) =>
                interpret(set).narrowMatch:
                  case TLAValueSet(set) =>
                    Some:
                      acc.flatMap: accMap =>
                        set.view.map(v =>
                          accMap.updated(TLAValueString(name.id), v)
                        )
            .get
            .map(TLAValueFunction(_))
      case TLAQuantifiedChoose(TLAQuantifierBound(tpe, ids, set), body) =>
        val TLAValueSet(setValue) = interpret(set): @unchecked
        setValue
          .find: elem =>
            tpe match
              case TLAQuantifierBound.IdsType =>
                val List(id) = ids: @unchecked
                interpret(body)(using env.updated(ById(id), elem)).narrowMatch:
                  case TLAValueBool(value) => value
              case TLAQuantifierBound.TupleType =>
                elem.narrowMatch:
                  case TLAValueTuple(elems) if elems.size == ids.size =>
                    interpret(body)(using
                      env ++ (ids.view.map(ById(_)) `zip` elems)
                    ).narrowMatch:
                      case TLAValueBool(value) => value
          .getOrElse(throw TypeError().ensureNodeInfo(set))
  }
}
