package pgo.util

import pgo.model.{RefersTo, Rewritable}
import pgo.model.mpcal._
import pgo.model.pcal._
import pgo.model.tla._
import pgo.util.CriticalSectionInterpreter.EvalContext.StateInfo
import pgo.util.MPCalPassUtils.MappedRead
import pgo.util.TLAExprInterpreter.{TLAValue, TLAValueBool, TLAValueFunction, TLAValueModel, TLAValueSet, TLAValueString, TLAValueTuple, TypeError}

import scala.collection.mutable
import scala.util.{Failure, Success}

object CriticalSectionInterpreter {
  sealed trait CSAtom {
    final def asCSElement: CSElement =
      this match {
        case elem: CSRead => elem
        case elem: CSWrite => elem
      }
  }
  object CSAtom {
    def fromJSON(v: ujson.Value): CSAtom =
      CSElement.fromJSON(v) match {
        case atom: CSRead => atom
        case atom: CSWrite => atom
        case _ => ???
      }
  }

  sealed abstract class CSElement
  case object CSAbridged extends CSElement
  final case class CSRead(name: EvalState.Identifier, indices: List[TLAValue], value: TLAValue) extends CSElement with CSAtom
  final case class CSWrite(name: EvalState.Identifier, indices: List[TLAValue], value: TLAValue) extends CSElement with CSAtom
  final case class CSDisorderedAtoms(elements: Set[CSAtom]) extends CSElement

  object CSElement {
    def fromJSON(v: ujson.Value): CSElement =
      v("tag").str match {
        case "abridged" => CSAbridged
        case "read" =>
          CSRead(
            name = EvalState.Identifier.fromJSON(v("name")),
            indices = v("indices").arr.view.map(v => TLAValue.parseFromString(v.str)).toList,
            value = TLAValue.parseFromString(v("value").str))
        case "write" =>
          CSWrite(
            name = EvalState.Identifier.fromJSON(v("name")),
            indices = v("indices").arr.view.map(v => TLAValue.parseFromString(v.str)).toList,
            value = TLAValue.parseFromString(v("value").str))
        case "disordered" =>
          CSDisorderedAtoms(
            v("atoms").arr.view.map(CSAtom.fromJSON).toSet)
        case _ => ???
      }
  }

  sealed abstract class ResultBranch[+T]
  final case class ResultBranchOK[+T](elements: LazyList[CSElement], value: T) extends ResultBranch[T]
  final case class ResultBranchJumped[+T](elements: LazyList[CSElement], value: T) extends ResultBranch[T]
  final case class ResultBranchCrashed(elements: LazyList[CSElement], err: Throwable) extends ResultBranch[Nothing]

  final class Result[+T](val outcomes: LazyList[ResultBranch[T]]) {
    def dropElements: Result[T] =
      new Result(outcomes.map {
        case ResultBranchOK(elements, value) => ResultBranchOK(LazyList.empty, value)
        case ResultBranchJumped(elements, value) => ResultBranchJumped(LazyList.empty, value)
        case ResultBranchCrashed(elements, err) => ResultBranchCrashed(LazyList.empty, err)
      })

    def map[U](fn: T => U): Result[U] =
      new Result(outcomes.map {
        case ResultBranchOK(elements, value) => ResultBranchOK(elements, fn(value))
        case ResultBranchJumped(elements, value) => ResultBranchJumped(elements, fn(value))
        case branch: ResultBranchCrashed => branch
      })

    def flatMap[U](fn: T => Result[U]): Result[U] =
      new Result(
        outcomes.flatMap {
          case ResultBranchOK(leftElements, value) =>
            fn(value)
              .outcomes
              .map {
                case ResultBranchOK(rightElements, value) => ResultBranchOK(leftElements #::: rightElements, value)
                case ResultBranchJumped(rightElements, value) => ResultBranchJumped(leftElements #::: rightElements, value)
                case ResultBranchCrashed(rightElements, err) => ResultBranchCrashed(leftElements #::: rightElements, err)
              }
          case ResultBranchJumped(leftElements, value) =>
            fn(value)
              .outcomes
              .map {
                case ResultBranchOK(rightElements, value) => ResultBranchJumped(leftElements #::: rightElements, value)
                case ResultBranchCrashed(rightElements, err) =>
                  assert(rightElements.isEmpty)
                  ResultBranchCrashed(leftElements, err)
                case _ => !!!
              }
          case crash: ResultBranchCrashed => Some(crash)
        })

    def ||[U >: T](other: Result[U]): Result[U] =
      new Result(outcomes #::: other.outcomes)
  }

  object Result {
    def apply[T](value: T): Result[T] =
      new Result(ResultBranchOK(LazyList.empty, value) #:: LazyList.empty)

    def withElements(elements: CSElement*): Result[Unit] =
      new Result(ResultBranchOK(elements.to(LazyList), ()) #:: LazyList.empty)

    def jumped[T](value: T): Result[T] =
      new Result(ResultBranchJumped(LazyList.empty, value) #:: LazyList.empty)

    def crashed(err: Throwable): Result[Nothing] =
      new Result(ResultBranchCrashed(LazyList.empty, err) #:: LazyList.empty)

    def empty: Result[Nothing] =
      new Result(LazyList.empty)
  }

  implicit class IterableResultOps[T](results: Iterable[Result[T]]) {
    def flattenResults: Result[T] =
      new Result(results.view.flatMap(_.outcomes).to(LazyList))
  }

  final case class EvalState(state: Map[EvalState.Identifier,TLAValue]) {
    def get(identifier: EvalState.Identifier): Option[TLAValue] =
      state.get(identifier)
  }

  object EvalState {
    final case class Identifier(prefix: String, name: String, selfOpt: Option[TLAValue])
    object Identifier {
      def fromJSON(v: ujson.Value): Identifier =
        Identifier(
          prefix = v("prefix").str,
          name = v("name").str,
          selfOpt = if(v.obj.contains("self")) Some(TLAValue.parseFromString(v("self").str)) else None)
    }
  }

  sealed abstract class Eval[+T] { self =>
    def apply(state: EvalState): Result[(EvalState,T)]

    final def dropElements: Eval[T] =
      Eval { state =>
        self(state).dropElements
      }

    final def map[U](fn: T => U): Eval[U] =
      Eval { state =>
        self(state).map {
          case (state, t) => (state, fn(t))
        }
      }

    final def flatMap[U](fn: T => Eval[U]): Eval[U] =
      Eval { state =>
        self(state).flatMap {
          case (state, t) => fn(t)(state)
        }
      }

    final def ||[U >: T](other: Eval[U]): Eval[U] =
      Eval { state =>
        self(state) || other(state)
      }
  }

  object Eval {
    def apply[T](fn: EvalState => Result[(EvalState,T)]): Eval[T] =
      new Eval[T] {
        override def apply(ctx: EvalState): Result[(EvalState, T)] = fn(ctx)
      }

    def value[T](t: =>T): Eval[T] =
      Eval { state =>
        Result((state, t))
      }

    val empty: Eval[Nothing] =
      Eval(_ => Result.empty)

    val unit: Eval[Unit] = value(())

    val jumped: Eval[Unit] = withResult(Result.jumped(()))

    def transformState(fn: EvalState => EvalState): Eval[Unit] =
      Eval { state =>
        Result((fn(state), ()))
      }

    def readState[T](fn: EvalState => T): Eval[T] =
      Eval { state =>
        Result((state, fn(state)))
      }

    def readState(name: EvalState.Identifier, indices: List[TLAValue])(implicit ctx: EvalContext): Eval[TLAValue] = {
      def impl(indices: List[TLAValue]): Eval[TLAValue] =
        indices match {
          case Nil => readState(_.state(name))
          case index :: restIndices =>
            readState(name, restIndices)
              .map {
                case TLAValueFunction(value) => value(index)
                case _ => !!!
              }
        }

      for {
        value <- impl(indices)
        _ <- ctx.mappingMacroInfoOpt match {
          case None => Eval.withElements(CSRead(name, indices, value))
          case Some(_) => Eval.unit
        }
      } yield value
    }

    def writeState(name: EvalState.Identifier, indices: List[TLAValue], value: TLAValue)(implicit ctx: EvalContext): Eval[Unit] = {
      def updateValue(value: =>TLAValue, indices: List[TLAValue], leaf: TLAValue): TLAValue =
        indices match {
          case Nil => leaf
          case index :: restIndices =>
            value match {
              case TLAValueFunction(value) =>
                TLAValueFunction(value.updated(index, updateValue(value(index), restIndices, leaf)))
              case _ => !!!
            }
        }

      for {
        _ <- transformState { state =>
          state.copy(state = state.state.updated(name, updateValue(state.state(name), indices, value)))
        }
        _ <- ctx.mappingMacroInfoOpt match {
          case None => withElements(CSWrite(name, indices, value))
          case Some(_) => Eval.unit
        }
      } yield ()
    }

    def crashed(err: Throwable): Eval[Nothing] =
      withResult(Result.crashed(err))

    def withResult[T](result: Result[T]): Eval[T] =
      Eval { state =>
        result.map((state, _))
      }

    def withElements(elements: CSElement*): Eval[Unit] =
      withResult(Result.withElements(elements:_*))
  }

  implicit class EvalIterableOperations[T](evals: Iterable[Eval[T]]) {
    def flattenEvals: Eval[Iterable[T]] = {
      def impl(evalList: List[Eval[T]], acc: List[T]): Eval[Iterable[T]] =
        evalList match {
          case Nil => Eval.value(evals.iterableFactory.from(acc.view.reverse))
          case eval :: restEvals =>
            eval.flatMap { value =>
              impl(restEvals, value :: acc)
            }
        }

      impl(evals.toList, Nil)
    }
  }

  final case class EvalContext(env: Map[ById[RefersTo.HasReferences],TLAValue],
                               containerName: String,
                               stateInfo: EvalContext.StateInfo,
                               mappingMacroInfoOpt: Option[EvalContext.MappingMacroInfo]) {
    def pcIdentifier: EvalState.Identifier =
      EvalState.Identifier("", ".pc", stateInfo.selfOpt)

    def stackIdentifier: EvalState.Identifier =
      EvalState.Identifier("", ".stack", stateInfo.selfOpt)

    def gotoTargetToPC(target: String): String =
      s"$containerName.$target"

    def withBinding(bind: ById[RefersTo.HasReferences], value: TLAValue): EvalContext =
      copy(env.updated(bind, value))

    def isStateVariable(ref: ById[RefersTo.HasReferences]): Boolean =
      stateInfo.stateBinds.get(ref) match {
        case None => false
        case Some(EvalContext.StateVariable(_)) => true
        case Some(_) => false
      }

    def hasMappingCount(ref: ById[RefersTo.HasReferences], count: Int): Boolean =
      stateInfo.mappingMacros.get(ref) match {
        case None => false
        case Some((_, actualCount)) => count == actualCount
      }

    def getStateReference(ref: ById[RefersTo.HasReferences]): EvalContext.StateReference =
      stateInfo.stateBinds.getOrElse(ref, EvalContext.NotState)

    def withMappingMacroInfo(info: EvalContext.MappingMacroInfo): EvalContext = {
      assert(mappingMacroInfoOpt.isEmpty)
      copy(mappingMacroInfoOpt = Some(info))
    }

    def mappingMacroInfo: EvalContext.MappingMacroInfo =
      mappingMacroInfoOpt.get
  }

  object EvalContext {
    sealed abstract class StateReference
    case object NotState extends StateReference
    final case class StateVariable(name: EvalState.Identifier) extends StateReference
    final case class MappedVariable(mappingMacro: MPCalMappingMacro, underlying: EvalState.Identifier) extends StateReference

    sealed abstract class MappingMacroInfo
    final case class MappingMacroReadInfo(underlying: EvalState.Identifier, indices: List[TLAValue]) extends MappingMacroInfo
    final case class MappingMacroWriteInfo(underlying: EvalState.Identifier, indices: List[TLAValue], value: TLAValue) extends MappingMacroInfo

    final case class StateInfo(selfOpt: Option[TLAValue],
                               stateBinds: Map[ById[RefersTo.HasReferences],EvalContext.StateReference],
                               mappingMacros: Map[ById[RefersTo.HasReferences],(MPCalMappingMacro,Int)]) {
      def self: TLAValue = selfOpt.get
    }
  }

  def interpretStmts(stmts: List[PCalStatement])(implicit ctx: EvalContext): Eval[Option[TLAValue]] =
    stmts match {
      case Nil => Eval.value(None)
      case PCalExtensionStatement(MPCalYield(expr)) :: restStmts =>
        assert(restStmts.isEmpty)
        ctx.mappingMacroInfo match {
          case EvalContext.MappingMacroReadInfo(_, _) =>
            readExpr(expr).map(Some(_))
          case EvalContext.MappingMacroWriteInfo(underlying, indices, _) =>
            for {
              yieldedValue <- readExpr(expr)
              _ <- Eval.writeState(underlying, indices, yieldedValue).map(_ => None)
            } yield None
        }
      case PCalGoto(target) :: Nil =>
        for {
          _ <- Eval.writeState(ctx.pcIdentifier, Nil, TLAValueString(ctx.gotoTargetToPC(target)))
          _ <- Eval.jumped
        } yield None
      case PCalReturn() :: Nil =>
        for {
          stackVal <- Eval.readState(ctx.stackIdentifier, Nil)
            .map { case TLAValueTuple(stackVal) => stackVal }
          _ <- Eval.writeState(ctx.stackIdentifier, Nil, TLAValueTuple(stackVal.tail))
          _ <- stackVal.head match {
            case TLAValueFunction(pairs) =>
              pairs.view
                .map {
                  case (TLAValueString(name), oldValue) =>
                    Eval.writeState(???, Nil, oldValue)
                }
                .foldLeft(Eval.unit) { (acc, ev) =>
                  acc.flatMap(_ => ev)
                }
            case _ => !!!
          }
          _ <- Eval.jumped
        } yield None
      case PCalExtensionStatement(call@MPCalCall(_, arguments)) :: (tailStmt@(PCalReturn() | PCalGoto(_))) :: restStmts =>
        assert(restStmts.isEmpty)
        ???
//        call.refersTo.params.view
//          .map {
//            case MPCalRefParam(name, mappingCount) => ???
//            case MPCalValParam(name) => ???
//          }
      case stmt :: restStmts =>
        for {
          firstResult <- interpretStmt(stmt)
          secondResult <- interpretStmts(restStmts)(ctx)
        } yield (firstResult match {
          case None => secondResult
          case Some(value) =>
            assert(secondResult.isEmpty)
            Some(value)
        })
    }

  def interpretExpr(expr: TLAExpression)(implicit ctx: EvalContext): Eval[TLAValue] =
    TLAExprInterpreter.interpret(expr)(ctx.env)
      .outcomes
      .map {
        case Failure(exception) => Eval.crashed(exception)
        case Success(value) => Eval.value(value)
      }
      .foldLeft(Eval.empty: Eval[TLAValue])(_ || _)

  def readExpr(expr: TLAExpression)(implicit ctx: EvalContext): Eval[TLAValue] = {
    val reads = mutable.ListBuffer.empty[(ById[RefersTo.HasReferences],Eval[TLAValue])]
    def mkReplacementValue(valueEval: Eval[TLAValue]): TLAExpression = {
      val decl = PCalVariableDeclarationEmpty(TLAIdentifier("<replaced>"))
      reads += ((ById(decl), valueEval))
      TLAGeneralIdentifier(TLAIdentifier("<replaced>"), Nil)
        .setRefersTo(decl)
    }

    lazy val readReplacer: PartialFunction[Rewritable,Rewritable] = {
      case TLAExtensionExpression(MPCalDollarValue()) =>
        mkReplacementValue {
          ctx.mappingMacroInfo match {
            case EvalContext.MappingMacroReadInfo(_, _) => !!!
            case EvalContext.MappingMacroWriteInfo(_, _, value) =>
              Eval.value(value)
          }
        }

      case TLAExtensionExpression(MPCalDollarVariable()) =>
        mkReplacementValue {
          ctx.mappingMacroInfo match {
            case EvalContext.MappingMacroReadInfo(underlying, indices) =>
              Eval.readState(underlying, indices)
            case EvalContext.MappingMacroWriteInfo(underlying, indices, _) =>
              Eval.readState(underlying, indices)
          }
        }

      case expr@MappedRead(mappingCount, ident) if ctx.hasMappingCount(ById(ident.refersTo), mappingCount) =>
        val indices = MPCalPassUtils.findMappedReadIndices(expr, mutable.ListBuffer.empty)
          .map(_.rewrite(Rewritable.TopDownFirstStrategy)(readReplacer))

        mkReplacementValue {
          indices
            .map(interpretExpr)
            .flattenEvals
            .map(_.toList)
            .flatMap { indexValues =>
              val EvalContext.MappedVariable(mappingMacro, underlying) = ctx.getStateReference(ById(ident.refersTo))
              interpretStmts(mappingMacro.readBody)(
                ctx
                  .withMappingMacroInfo(EvalContext.MappingMacroReadInfo(
                    underlying = underlying,
                    indices = indexValues)))
                .map(_.get)
            }
        }

      case ident@TLAGeneralIdentifier(_, prefix) if ctx.isStateVariable(ById(ident.refersTo)) =>
        assert(prefix.isEmpty)
        mkReplacementValue {
          val EvalContext.StateVariable(stateName) = ctx.getStateReference(ById(ident.refersTo))
          Eval.readState(stateName, Nil)
        }
    }

    val exprWithReads = expr.rewrite(Rewritable.TopDownFirstStrategy)(readReplacer)

    def interpretWithAllReads(reads: List[(ById[RefersTo.HasReferences],Eval[TLAValue])])(implicit ctx: EvalContext): Eval[TLAValue] =
      reads match {
        case Nil => interpretExpr(exprWithReads)
        case (id, eval) :: restReplacements =>
          eval.flatMap { value =>
            interpretWithAllReads(restReplacements)(ctx.withBinding(id, value))
          }
      }

    interpretWithAllReads(reads.result())
  }

  def interpretStmt(stmt: PCalStatement)(implicit ctx: EvalContext): Eval[Option[TLAValue]] =
    stmt match {
      case PCalExtensionStatement(MPCalCall(_, _)) => !!!
      case PCalAssert(condition) =>
        readExpr(condition).flatMap {
          case TLAValueBool(true) => Eval.value(None)
          case _ => Eval.crashed(TypeError())
        }
      case PCalAssignment(List(PCalAssignmentPair(lhs, rhs))) =>
        def findLhsInfo(lhs: PCalAssignmentLhs, acc: List[TLAValue]): Eval[(List[TLAValue],EvalContext.StateReference)] =
          lhs match {
            case ident@PCalAssignmentLhsIdentifier(_) =>
              Eval.value((acc, ctx.getStateReference(ById(ident.refersTo))))
            case PCalAssignmentLhsProjection(lhs, projections) =>
              projections.view
                .map(readExpr)
                .flattenEvals
                .flatMap {
                  case indices if indices.size == 1 =>
                    findLhsInfo(lhs, indices.head :: acc)
                  case indices =>
                    findLhsInfo(lhs, TLAValueTuple(indices.toVector) :: acc)
                }
            case PCalAssignmentLhsExtension(MPCalDollarVariable()) =>
              assert(acc.isEmpty) // not sure when this might be reasonably false, hopefully never
              ctx.mappingMacroInfo match {
                case EvalContext.MappingMacroReadInfo(underlying, indices) =>
                  Eval.value((indices, EvalContext.StateVariable(underlying)))
                case EvalContext.MappingMacroWriteInfo(underlying, indices, _) =>
                  Eval.value((indices, EvalContext.StateVariable(underlying)))
              }
            case _ => !!!
          }

        for {
          rhsVal <- readExpr(rhs)
          info <- findLhsInfo(lhs, Nil)
          (indices, stateInfo) = info
          _ <- stateInfo match {
            case EvalContext.NotState => !!!
            case EvalContext.StateVariable(name) =>
              Eval.writeState(name, indices, rhsVal)
            case EvalContext.MappedVariable(mappingMacro, underlying) =>
              interpretStmts(mappingMacro.writeBody)(
                ctx
                  .withMappingMacroInfo(EvalContext.MappingMacroWriteInfo(
                    underlying = underlying,
                    indices = indices,
                    value = rhsVal)))
                .map { result =>
                  assert(result.isEmpty)
                  result
                }
                .flatMap(_ => Eval.withElements(CSWrite(underlying, indices, rhsVal)))
          }
        } yield None
      case PCalAwait(condition) =>
        readExpr(condition).flatMap {
          case TLAValueBool(true) => Eval.value(None)
          case TLAValueBool(false) => Eval.empty
          case _ => Eval.crashed(TypeError())
        }
      case PCalCall(_, _) => !!!
      case PCalEither(cases) =>
        cases.view
          .map(interpretStmts)
          .reduce(_ || _)
      case PCalGoto(_) => !!!
      case PCalIf(condition, yes, no) =>
        readExpr(condition).flatMap {
          case TLAValueBool(true) =>
            interpretStmts(yes)
          case TLAValueBool(false) =>
            interpretStmts(no)
          case _ =>
            Eval.crashed(TypeError())
        }
      case PCalLabeledStatements(_, _) => !!!
      case PCalMacroCall(_, _) => !!!
      case PCalPrint(value) =>
        readExpr(value).map(_ => None)
      case PCalReturn() => !!!
      case PCalSkip() =>
        Eval.value(None)
      case PCalWhile(_, _) => !!!
      case PCalWith(variables, body) =>
        def impl(variables: List[PCalVariableDeclarationBound])(implicit ctx: EvalContext): Eval[Option[TLAValue]] =
          variables match {
            case Nil => interpretStmts(body)
            case decl :: restDecls =>
              decl match {
                case decl@PCalVariableDeclarationValue(_, value) =>
                  readExpr(value).flatMap { value =>
                    impl(restDecls)(ctx.withBinding(ById(decl), value))
                  }
                case decl@PCalVariableDeclarationSet(_, set) =>
                  readExpr(set).flatMap {
                    case TLAValueSet(set) =>
                      set.view
                        .map { value =>
                          impl(restDecls)(ctx.withBinding(ById(decl), value))
                        }
                        .foldLeft(Eval.empty: Eval[Option[TLAValue]])(_ || _)
                    case _ =>
                      Eval.crashed(TypeError())
                  }
              }
          }

        impl(variables)
      case _ => !!!
    }

  def interpretStateVarDecls(decls: List[PCalVariableDeclaration])(implicit ctx: EvalContext): Eval[Unit] =
    decls match {
      case Nil => Eval.value(())
      case decl :: restDecls =>
        val result = decl match {
          case PCalVariableDeclarationEmpty(name) =>
            Eval.writeState(EvalState.Identifier(ctx.containerName, name.id, ctx.stateInfo.selfOpt), Nil, TLAValueModel("defaultInitValue"))
          case PCalVariableDeclarationValue(name, value) =>
            readExpr(value).flatMap { value =>
              Eval.writeState(EvalState.Identifier(ctx.containerName, name.id, ctx.stateInfo.selfOpt), Nil, value)
            }
          case PCalVariableDeclarationSet(name, set) =>
            readExpr(set).flatMap {
              case TLAValueSet(set) =>
                set.view
                  .map { value =>
                    Eval.writeState(EvalState.Identifier(ctx.containerName, name.id, ctx.stateInfo.selfOpt), Nil, value)
                  }
                  .foldLeft(Eval.empty: Eval[Unit])(_ || _)
              case _ =>
                !!!
            }
        }
        result.flatMap(_ => interpretStateVarDecls(restDecls))
    }

  class StateStepper private (mpcalBlock: MPCalBlock, constants: Map[ById[RefersTo.HasReferences],TLAValue]) {
    private lazy val selfDecls: Set[ById[RefersTo.HasReferences]] =
      (mpcalBlock.instances.view.map(_.selfDecl) ++
        mpcalBlock.archetypes.view.map(_.selfDecl) ++
        mpcalBlock.mpcalProcedures.view.map(_.selfDecl))
        .map(ById(_))
        .toSet

    private def evalStep(pc: String, self: TLAValue, stateInfo: StateInfo)(implicit ctx: EvalContext): Eval[Unit] = {
      val block = pcBlocks(pc)

      for {
        _ <- Eval.withElements(CSRead(ctx.pcIdentifier, Nil, TLAValueString(pc)))
        result <- interpretStmts(block)
      } yield {
        assert(result.isEmpty)
        ()
      }
    }

    lazy val initStates: LazyList[EvalState] = {
      implicit val ctx: EvalContext = EvalContext(
        env = constants,
        containerName = "",
        stateInfo = StateInfo(
          selfOpt = None,
          stateBinds = Map.empty,
          mappingMacros = Map.empty),
        mappingMacroInfoOpt = None)
      val initEvalState: EvalState = EvalState(Map.empty)

      interpretStateVarDecls(mpcalBlock.variables)
        .apply(initEvalState)
        .outcomes
        .map {
          case ResultBranchOK(_, (state, ())) => state
          case ResultBranchJumped(elements, value) => ???
          case ResultBranchCrashed(elements, err) => ???
        }
    }

    def step(archetypeName: String, self: TLAValue)(state: EvalState): LazyList[StateStepper.StepOutcome] = {
      val stateInfo = stateInfoByArchetype(archetypeName)(self)

      val initCtx: EvalContext = EvalContext(
        env = constants ++ selfDecls.view.map(_ -> self),
        containerName = "", // temp value, must be overwritten before passing ctx to anything
        stateInfo = stateInfo,
        mappingMacroInfoOpt = None)

      val eval = for {
        pc <- Eval.readState(_.state.get(initCtx.pcIdentifier))
          .flatMap {
            case Some(pc) => Eval.value(pc)
            case None =>
              implicit val ctx: EvalContext = initCtx.copy(containerName = archetypeName)
              val arch = archetypesByName(archetypeName)
              val initialPC = TLAValueString(s"$archetypeName.${arch.body.head.asInstanceOf[PCalLabeledStatements].label.name}")
              val instance = instancesByName(archetypeName)
              for {
                _ <- Eval.transformState(_ => state)
                _ <- Eval.writeState(ctx.pcIdentifier, Nil, initialPC)
                _ <- instance.arguments.view
                  .zipWithIndex
                  .collect { case (Right(expr), index) => (expr, index) }
                  .foldLeft(Eval.unit) { (prev, pair) =>
                    val (expr, index) = pair
                    for {
                      _ <- prev
                      value <- interpretExpr(expr)
                      _ <- Eval.writeState(EvalState.Identifier(ctx.containerName, arch.params(index).canonicalIdString, ctx.stateInfo.selfOpt), Nil, value)
                    } yield ()
                  }
                _ <- interpretStateVarDecls(arch.variables)
              } yield initialPC
          }
          .dropElements // make sure we don't keep any preamble state writes
        _ <- Eval.withElements(CSRead(initCtx.pcIdentifier, Nil, pc))
        _ <- pc match {
          case TLAValueString(pc) =>
            implicit val ctx: EvalContext = initCtx.copy(containerName = containerNames(pc))
            evalStep(pc, self, stateInfo)
          case _ => !!!
        }
      } yield ()

      eval(state)
        .outcomes
        .map {
          case ResultBranchOK(_, _) => !!!
          case ResultBranchJumped(elements, (nextState, ())) =>
            StateStepper.StepValid(elements.toList, nextState)
          case ResultBranchCrashed(elements, err) =>
            StateStepper.StepInvalid(elements.toList, err)
        }
    }

    private lazy val archetypesByName: Map[String,MPCalArchetype] =
      mpcalBlock.archetypes.view
        .map(arch => arch.name.id -> arch)
        .toMap

    private lazy val pcBlocks: Map[String,List[PCalStatement]] = {
      val archPairs = mpcalBlock.archetypes.view
        .flatMap { arch =>
          arch.body.view
            .map(_.asInstanceOf[PCalLabeledStatements])
            .map { block =>
              s"${arch.name.id}.${block.label.name}" -> block.statements
            }
        }
      val procPairs = mpcalBlock.mpcalProcedures.view
        .flatMap { proc =>
          proc.body.view
            .map(_.asInstanceOf[PCalLabeledStatements])
            .map { block =>
              s"${proc.name.id}.${block.label.name}" -> block.statements
            }
        }

      (archPairs ++ procPairs).toMap
    }

    private lazy val containerNames: Map[String,String] =
      pcBlocks.view
        .map {
          case (pc, _) => pc -> pc.split(raw"\.").head
        }
        .toMap

    private lazy val instancesByName: Map[String,MPCalInstance] =
      mpcalBlock.instances.view
        .map(instance => instance.refersTo.name.id -> instance)
        .toMap

    private lazy val stateInfoByArchetype: Map[String,TLAValue => EvalContext.StateInfo] =
      mpcalBlock.instances.view
        .map { instance =>
          val archetype = instance.refersTo
          val archName = archetype.name.id
          archName -> { (self: TLAValue) =>
            val stateBinds: Map[ById[RefersTo.HasReferences],EvalContext.StateReference] = instance.mappings.view
              .flatMap { mapping =>
                val mappingMacro = mapping.refersTo
                val ref = archetype.params(mapping.target.position)
                (instance.arguments(mapping.target.position) match {
                  case Left(refExpr) =>
                    List(
                      ById(ref) -> EvalContext.MappedVariable(
                        mappingMacro = mappingMacro,
                        underlying = EvalState.Identifier("", refExpr.refersTo.canonicalIdString, None)))
                  case Right(_) =>
                    List(
                      ById(ref) -> EvalContext.StateVariable(
                        EvalState.Identifier(archName, ref.canonicalIdString, Some(self))))
                }).view ++ archetype.variables.view.map { decl =>
                  ById(decl) -> EvalContext.StateVariable(
                    EvalState.Identifier(archName, decl.canonicalIdString, Some(self)))
                }
              }
              .toMap
            val mappingMacros: Map[ById[RefersTo.HasReferences],(MPCalMappingMacro,Int)] = instance.mappings.view
              .map { mapping =>
                val mappingMacro = mapping.refersTo
                val ref = archetype.params(mapping.target.position)
                ById(ref) -> (mappingMacro, mapping.target.mappingCount)
              }
              .toMap

            EvalContext.StateInfo(
              selfOpt = Some(self),
              stateBinds = stateBinds,
              mappingMacros = mappingMacros)
          }
        }
        .toMap
  }

  object StateStepper {
    def apply(mpcalBlock: MPCalBlock, constants: Map[ById[RefersTo.HasReferences],TLAValue] = Map.empty): StateStepper =
      new StateStepper(mpcalBlock, constants)

    sealed abstract class StepOutcome
    final case class StepValid(elements: List[CSElement], nextState: EvalState) extends StepOutcome
    final case class StepInvalid(elements: List[CSElement], err: Throwable) extends StepOutcome
  }
}
