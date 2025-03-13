package pgo.tracing

import scala.collection.mutable

import pgo.model.mpcal.*
import pgo.model.tla.*
import pgo.model.pcal.*
import pgo.model.DefinitionOne
import pgo.model.Definition.ScopeIdentifierName
import pgo.trans.PCalRenderPass
import pgo.model.{Visitable, Rewritable}

object InferFromMPCal:
  def apply(
      mpcalBlock: MPCalBlock,
      tlaModule: TLAModule,
      destDir: os.Path,
  ): JSONToTLA =
    val varsInfo = mutable.HashMap[String, MPCalVariable]()
    val modelName = tlaModule.name.id

    mpcalBlock.variables.foreach: v =>
      assert(!varsInfo.contains(v.name.id))
      varsInfo(v.name.id) = MPCalVariable.Global(v.name.id)

    val tlaDefinitions = tlaModule.units.view
      .collect:
        case defn: TLAOperatorDefinition =>
          defn.name -> defn
      .toMap

    val necessaryTLADefinitions = mutable.HashSet[TLAOperatorDefinition]()
    val necessaryTLADefinitionSeqReversed =
      mutable.ListBuffer[TLAOperatorDefinition]()
    def ensureNecessaryTLADefinitions(tlaNode: TLANode): Unit =
      tlaNode.visit(strategy = Visitable.BottomUpFirstStrategy):
        case ident: TLAGeneralIdentifier =>
          val defn = ident.refersTo
          tlaDefinitions.get(defn.identifier) match
            case None =>
            case Some(defn) =>
              if !necessaryTLADefinitions(defn)
              then
                necessaryTLADefinitions += defn
                necessaryTLADefinitionSeqReversed += defn
                ensureNecessaryTLADefinitions(defn)

    final class FullNameCtx(archName: String):
      extension (ident: DefinitionOne)
        def fullName: String =
          s"$archName.${ident.identifier.asInstanceOf[ScopeIdentifierName].name.id}"
        def fullNameUnderscore: String =
          fullName.replace(".", "_")

    mpcalBlock.archetypes.foreach:
      case MPCalArchetype(name, selfDecl, params, variables, _) =>
        val archName = name.id
        given FullNameCtx = FullNameCtx(archName)

        params.foreach:
          case decl: MPCalRefParam =>
            assert(!varsInfo.contains(decl.fullName))
            varsInfo(decl.fullName) =
              MPCalVariable.Mapping(decl.fullNameUnderscore)
          case decl: MPCalValParam =>
            assert(!varsInfo.contains(decl.fullName))
            varsInfo(decl.fullName) = MPCalVariable.Local(decl.name.id)

        variables.foreach: decl =>
          assert(!varsInfo.contains(decl.fullName))
          varsInfo(decl.fullName) = MPCalVariable.Local(decl.name.id)

    val localIdxs = mutable.HashMap[String, Int]()
    def addLocalIdx(name: String): String =
      localIdxs.get(name) match
        case None =>
          localIdxs(name) = 0
          name
        case Some(idx) =>
          localIdxs(name) = idx + 1
          s"$name$idx"

    // Prefill local idxs with global vars, because global <-> local conflicts can happen
    mpcalBlock.variables.foreach: decl =>
      addLocalIdx(decl.name.id)

    val mappingMacroInstantiations = mutable.ArrayBuffer[List[String]]()

    mpcalBlock.instances.foreach:
      case inst @ MPCalInstance(_, _, archetypeName, arguments, mappings) =>
        val arch = inst.refersTo
        given FullNameCtx = FullNameCtx(arch.name.id)

        // Correct local var names: if they collide, add an incrementing counter
        // (this mimics a combination of the MPCal and PCal translators)
        val localVars =
          arch.params.collect { case param @ MPCalValParam(_) => param }
            ++ arch.variables
        localVars.foreach: v =>
          varsInfo(v.fullName) match
            case MPCalVariable.Local(tlaVar) =>
              varsInfo(v.fullName) = MPCalVariable.Local(addLocalIdx(tlaVar))
            case _ => // pass
        // instantiate referenced mapping macros
        val unmappedRefParams =
          arch.params.zipWithIndex
            .collect:
              case (param: MPCalRefParam, idx) => (param, idx)
            .to(mutable.HashMap)
        mappings.foreach:
          case mapping @ MPCalMapping(target, mappingMacroIdentifier) =>
            val refParam @ MPCalRefParam(paramName, _) =
              arch.params(target.position): @unchecked

            // not unmapped anymore
            unmappedRefParams -= refParam

        // If the param has no mapping, there is no mapping macro for it.
        // It will just act like a proxy to the global it's bound to, so change it to one accordingly.
        unmappedRefParams.view.toArray
          .sortInPlaceBy(_._1.name.id)
          .foreach:
            case (refParam, idx) =>
              inst.arguments(idx) match
                case Left(ref) =>
                  varsInfo(refParam.fullName) =
                    MPCalVariable.Global(ref.name.id)
                case Right(value) =>
                  // This is actually just an initialization of a local via param passing.
                  // It looks just like a local to us, so we can treat it like one.
                  varsInfo(refParam.fullName) =
                    MPCalVariable.Local(refParam.name.id)

    val stateVarNames =
      varsInfo.values.view
        .collect:
          case MPCalVariable.Global(tlaVar) => tlaVar
          case MPCalVariable.Local(tlaVar)  => tlaVar
        .toSet

    mpcalBlock.instances.foreach:
      case inst @ MPCalInstance(_, _, archetypeName, arguments, mappings) =>
        val arch = inst.refersTo
        given FullNameCtx = FullNameCtx(arch.name.id)

        mappings.foreach:
          case mapping @ MPCalMapping(target, mappingMacroIdentifier) =>
            val refParam @ MPCalRefParam(paramName, _) =
              arch.params(target.position): @unchecked
            val stateVar = inst.arguments(target.position) match
              case Left(MPCalRefExpr(name, _)) => name.id
              case Right(expr)                 => ???

            val mappingMacro = mapping.refersTo

            mappingMacroInstantiations += compileMappingMacroDefns(
              namePrefix = refParam.fullNameUnderscore,
              stateVar = stateVar,
              mappingMacro = mappingMacro,
              mappingCount = target.mappingCount,
              stateVarNames = stateVarNames,
              ensureNecessaryTLADefinitions = ensureNecessaryTLADefinitions,
            )

    var config = JSONToTLA(
      modelName = tlaModule.name.id,
      destDir = destDir,
    )
    config = tlaModule.exts.foldLeft(config):
      case (config, moduleRef) =>
        config.withTLAExtends(moduleRef.identifier.name.id)
    config = necessaryTLADefinitionSeqReversed.reverseIterator
      .foldLeft(config):
        case (config, defn) =>
          val descr = PCalRenderPass.describeUnit(defn)
          config.withAdditionalDefns(
            descr.linesIterator.concat(List("")).toList,
          )
    config =
      config.withAdditionalDefns(mappingMacroInstantiations.view.flatten.toList)
    config = mpcalBlock.variables.foldLeft(config):
      case (config, decl) =>
        config.modelVariable(decl.name.id)
    tlaModule.visit(strategy = Visitable.TopDownFirstStrategy):
      case TLAConstantDeclaration(constants) =>
        constants.foreach:
          case TLAOpDecl(TLAOpDecl.NamedVariant(name, 0)) =>
            config = config.tlaConstant(name.id)
          case _ => ???
    config = varsInfo.foldLeft(config):
      case (config, (mpcalName, info)) =>
        info match
          case MPCalVariable.Local(tlaVar) =>
            config.mpcalLocal(mpcalName, tlaVar)
          case MPCalVariable.Global(tlaVar) =>
            config.mpcalGlobal(mpcalName, tlaVar)
          case MPCalVariable.Mapping(tlaOperatorPrefix) =>
            config.mpcalMacro(mpcalName, tlaOperatorPrefix)

    config
  end apply

  private def compileMappingMacroDefns(
      namePrefix: String,
      stateVar: String,
      mappingMacro: MPCalMappingMacro,
      mappingCount: Int,
      stateVarNames: Set[String],
      ensureNecessaryTLADefinitions: TLANode => Unit,
  ): List[String] =
    require(mappingCount >= 0)

    enum Compilation[+T]:
      case GetStateName extends Compilation[String]
      case GetNextStateName extends Compilation[String]
      case Write(str: String) extends Compilation[Unit]
      case NewLine extends Compilation[Unit]

      case IncState(comp: Compilation[T])
      case GetIndent extends Compilation[Int]
      case IndentAt(comp: Compilation[T], position: Int)
      case IndentHere(comp: Compilation[T], offset: Int)

      case Pure(value: T)
      case FlatMap[T, U](lhs: Compilation[T], fn: T => Compilation[U])
          extends Compilation[U]

      def map[U](fn: T => U): Compilation[U] =
        flatMap(t => Pure(fn(t)))

      def flatMap[U](fn: T => Compilation[U]): Compilation[U] =
        FlatMap(this, fn)

      def *>[U](comp: => Compilation[U]): Compilation[U] =
        for _ <- this; u <- comp yield u

      def perform(): (T, List[String]) =
        enum Instruction:
          case Continuation(fn: Any => Compilation[Any])
          case RestoreIndent(prevIndent: Int)
          case RestoreStateIdx(prevStateIdx: Int)

        val stack = mutable.ArrayDeque[Instruction]()
        val linesAcc = mutable.ListBuffer[String]()
        val currentLine = StringBuilder()
        var returnValue: Any = ()
        var stateIdx = 0
        var indent = 0

        @scala.annotation.tailrec
        def impl[T](self: Compilation[T]): Unit =
          self match
            case GetStateName =>
              returnValue = s"__state$stateIdx"
            case GetNextStateName =>
              returnValue = s"__state${stateIdx + 1}"
            case Write(str) =>
              assert(!str.contains('\n'))
              if str.nonEmpty
              then
                if currentLine.isEmpty
                then currentLine ++= (0 until indent).view.map(_ => ' ')
                currentLine ++= str
              returnValue = ()
            case NewLine =>
              linesAcc += currentLine.result()
              currentLine.clear()
              returnValue = ()
            case IncState(comp) =>
              stack += Instruction.RestoreStateIdx(stateIdx)
              stateIdx += 1
              impl(comp)
            case GetIndent =>
              returnValue = indent.max(currentLine.size)
            case IndentAt(comp, position) =>
              stack += Instruction.RestoreIndent(indent)
              indent = position
              impl(comp)
            case IndentHere(comp, offset) =>
              stack += Instruction.RestoreIndent(indent)
              indent = indent.max(currentLine.size + offset)
              impl(comp)
            case Pure(value) =>
              returnValue = value
            case FlatMap(lhs, fn) =>
              stack += Instruction.Continuation(fn.asInstanceOf)
              impl(lhs)

        impl(this)
        while stack.nonEmpty
        do
          stack.removeLast() match
            case Instruction.Continuation(fn) =>
              impl(fn(returnValue))
            case Instruction.RestoreIndent(prevIndent) =>
              indent = prevIndent
            case Instruction.RestoreStateIdx(prevStateIdx) =>
              stateIdx = prevStateIdx
        end while

        if currentLine.nonEmpty
        then linesAcc += currentLine.result()

        (returnValue.asInstanceOf[T], linesAcc.result())
      end perform

    object Compilation:
      lazy val unit: Compilation[Unit] = Compilation.Pure(())
      lazy val stateName: Compilation[String] = Compilation.GetStateName
      lazy val nextStateName: Compilation[String] = Compilation.GetNextStateName
      def write(str: String): Compilation[Unit] = Compilation.Write(str)
      lazy val newLine: Compilation[Unit] = Compilation.NewLine

      lazy val getIndent: Compilation[Int] = Compilation.GetIndent
      def indentAt[T](position: Int)(comp: Compilation[T]): Compilation[T] =
        Compilation.IndentAt(comp, position)
      def indentHere[T](comp: Compilation[T]): Compilation[T] =
        Compilation.IndentHere(comp, offset = 0)

      def indentHereOffset[T](offset: Int)(
          comp: Compilation[T],
      ): Compilation[T] =
        Compilation.IndentHere(comp, offset = offset)

      def incState[T](comp: Compilation[T]): Compilation[T] =
        Compilation.IncState(comp)

      extension (list: List[PCalStatement])
        def renderConjunction(
            rest: Ctx ?=> Compilation[Unit],
        )(using Yielder, Ctx): Compilation[Unit] =
          list match
            case Nil => rest
            case stmt :: stmts =>
              renderPCalStatement(stmt, stmts.renderConjunction(rest))
    end Compilation

    import Compilation.*

    sealed abstract class Yielder:
      def apply(expr: TLAExpression, rest: Ctx ?=> Compilation[Unit])(using
          Ctx,
      ): Compilation[Unit]

    inline def yielder(using yielder: Yielder): Yielder = yielder

    sealed abstract class Ctx:
      def putConjunct(
          conj: Ctx ?=> Compilation[Unit],
          after: Ctx ?=> Compilation[Unit],
      ): Compilation[Unit]
      def putBinding(
          comp: Ctx ?=> Compilation[Unit],
          after: Ctx ?=> Compilation[Unit],
      ): Compilation[Unit]

    object Ctx:
      object Init extends Ctx:
        def putConjunct(
            conj: (Ctx) ?=> Compilation[Unit],
            after: (Ctx) ?=> Compilation[Unit],
        ): Compilation[Unit] =
          indentHere:
            write("/\\ ")
              *> indentHere(conj(using Init))
              *> after(using Conj)
        def putBinding(
            comp: (Ctx) ?=> Compilation[Unit],
            after: (Ctx) ?=> Compilation[Unit],
        ): Compilation[Unit] =
          getIndent.flatMap: indent =>
            write("LET ")
              *> indentHere(comp(using Init))
              *> after(using Let(baseIndent = indent))

      final case class Let(baseIndent: Int) extends Ctx:
        def putConjunct(
            conj: (Ctx) ?=> Compilation[Unit],
            after: (Ctx) ?=> Compilation[Unit],
        ): Compilation[Unit] =
          newLine
          *> indentAt(position = baseIndent):
            write("IN  ")
            *> indentHere:
              Init.putConjunct(conj, after)

        def putBinding(
            comp: (Ctx) ?=> Compilation[Unit],
            after: (Ctx) ?=> Compilation[Unit],
        ): Compilation[Unit] =
          newLine
          *> indentAt(position = baseIndent + 4):
            comp(using Init)
          *> after(using this)

      object Conj extends Ctx:
        def putConjunct(
            conj: (Ctx) ?=> Compilation[Unit],
            after: (Ctx) ?=> Compilation[Unit],
        ): Compilation[Unit] =
          newLine
            *> write("/\\ ")
            *> indentHere(conj(using Init))
            *> after(using Conj)

        def putBinding(
            comp: (Ctx) ?=> Compilation[Unit],
            after: (Ctx) ?=> Compilation[Unit],
        ): Compilation[Unit] =
          newLine
            *> write("/\\ ")
            *> indentHere(Init.putBinding(comp, after))

    inline def ctx(using ctx: Ctx): Ctx = ctx

    def renderTLAExpr(expr: TLAExpression): Compilation[Unit] =
      indentHere:
        stateName.flatMap: stateName =>
          ensureNecessaryTLADefinitions(expr)
          // actual transform
          val dummyIdent = TLADefiningIdentifier(TLAIdentifier("???"))
          val exprWithoutDollars =
            expr.rewrite(strategy = Rewritable.BottomUpOnceStrategy):
              case TLAExtensionExpression(MPCalDollarValue()) =>
                TLAGeneralIdentifier(TLAIdentifier("__value"), Nil).setRefersTo(
                  dummyIdent,
                )
              case TLAExtensionExpression(MPCalDollarVariable()) =>
                val state = TLAGeneralIdentifier(TLAIdentifier(stateName), Nil)
                  .setRefersTo(dummyIdent)
                val stateIndexed =
                  TLAFunctionCall(state, List(TLAString(stateVar)))
                (0 until mappingCount).foldLeft[TLAExpression](stateIndexed):
                  (acc, idx) =>
                    TLAFunctionCall(
                      acc,
                      List(
                        TLAGeneralIdentifier(TLAIdentifier(s"__idx$idx"), Nil)
                          .setRefersTo(dummyIdent),
                      ),
                    )

          PCalRenderPass
            .describeExpr(exprWithoutDollars)
            .linesIterator
            .map(write)
            .reduce(_ *> newLine *> _)

    def renderPCalStatement(
        stmt: PCalStatement,
        rest: Ctx ?=> Compilation[Unit],
    )(using Yielder, Ctx): Compilation[Unit] =
      stmt match
        case PCalExtensionStatement(MPCalYield(expr)) =>
          yielder(expr, rest)
        case PCalAssert(condition) =>
          ctx.putConjunct(
            conj = write("Assert(")
              *> renderTLAExpr(condition)
              *> write(
                s", \"assertion failed! (${condition.sourceLocation.shortDescription.linesIterator.mkString("\\n")})\")",
              ),
            after = rest,
          )
        case PCalAssignment(pairs) =>
          stateName.flatMap: stateName =>
            nextStateName.flatMap: nextStateName =>
              ctx.putBinding(
                comp = write(nextStateName)
                  *> write(" == [")
                  *> indentHereOffset(offset = 2):
                    write(stateName)
                      *> write(" EXCEPT ")
                      *> pairs.view
                        .map:
                          case PCalAssignmentPair(lhs, rhs) =>
                            def renderLhs(
                                lhs: PCalAssignmentLhs,
                            ): Compilation[Unit] =
                              lhs match
                                case PCalAssignmentLhsIdentifier(identifier) =>
                                  write(".")
                                    *> write(identifier.id)
                                case PCalAssignmentLhsProjection(
                                      lhs,
                                      projections,
                                    ) =>
                                  renderLhs(lhs)
                                    *> write("[")
                                    *> projections.view
                                      .map(renderTLAExpr)
                                      .reduce(_ *> write(", ") *> _)
                                    *> write("]")
                                case PCalAssignmentLhsExtension(
                                      MPCalDollarVariable(),
                                    ) =>
                                  write(".")
                                    *> write(stateVar)
                                    *> indicesArgsApply
                                case PCalAssignmentLhsExtension(_) => ???

                            write("!")
                              *> renderLhs(lhs)
                              *> write(" = ")
                              *> renderTLAExpr(rhs)
                        .reduce(_ *> newLine *> _)
                      *> write("]")
                ,
                after = incState(rest),
              )
        case PCalAwait(condition) =>
          ctx.putConjunct(
            conj = renderTLAExpr(condition),
            after = rest,
          )
        case PCalEither(cases) =>
          ctx.putConjunct(
            conj = indentHere:
              cases.view
                .map: stmts =>
                  write("\\/ ")
                    *> indentHere(stmts.renderConjunction(rest))
                .reduce(_ *> newLine *> _)
            ,
            after = write(""),
          )
        case PCalIf(condition, yes, no) =>
          ctx.putConjunct(
            conj = write("IF   ")
              *> renderTLAExpr(condition)
              *> newLine
              *> write("THEN ")
              *> indentHere(yes.renderConjunction(rest))
              *> newLine
              *> write("ELSE ")
              *> indentHere(no.renderConjunction(rest)),
            after = write(""),
          )
        case PCalPrint(value) =>
          ctx.putConjunct(
            conj = write("PrintT(")
              *> renderTLAExpr(value)
              *> write(")"),
            after = rest,
          )
        case PCalSkip() =>
          rest
        case PCalWith(variables, body) =>
          variables.foldRight[Ctx ?=> Compilation[Unit]](
            body.renderConjunction(rest),
          ): (vrbl, accRight) =>
            vrbl match
              case PCalVariableDeclarationValue(name, value) =>
                ctx.putBinding(
                  comp = write(name.id)
                    *> write(" == ")
                    *> renderTLAExpr(value),
                  after = accRight,
                )
              case PCalVariableDeclarationSet(name, set) =>
                ctx.putConjunct(
                  conj = indentHere:
                    getIndent.flatMap: baseIndent =>
                      write("\\E ")
                        *> write(name.id)
                        *> write(" \\in ")
                        *> renderTLAExpr(set)
                        *> write(" :")
                        *> newLine
                        *> indentAt(position = baseIndent + 1):
                          accRight
                  ,
                  after = write(""),
                )

        case PCalExtensionStatement(_) => ??? // should be unreachable
        case PCalGoto(_) | PCalWhile(_, _) | PCalReturn() |
            PCalMacroCall(_, _) | PCalLabeledStatements(_, _) |
            PCalCall(_, _) =>
          ??? // doesn't make sense in context
          // (except maybe the macro call, but for now let's ignore that)

    lazy val indicesArgsDefns =
      (0 until mappingCount).view
        .foldRight(write("")): (idx, accRight) =>
          write(", ")
            *> write("__idx")
            *> write(idx.toString())
            *> accRight

    lazy val indicesArgsApply =
      (0 until mappingCount).view
        .map: idx =>
          write("[__idx")
            *> write(idx.toString())
            *> write("]")
        .reduceOption(_ *> _)
        .getOrElse(write(""))

    def dunderRestCall(using Ctx) =
      ctx.putConjunct(
        conj = stateName.flatMap: stateName =>
          write("__rest(")
            *> write(stateName)
            *> write(")"),
        after = write(""),
      )

    val compilation: Compilation[Unit] =
      write(namePrefix)
        *> write("_read(__state0, self")
        *> indicesArgsDefns
        *> write(", __value, __rest(_)) ==")
        *> newLine
        *> indentHereOffset(offset = 2) {
          given Yielder with
            def apply(expr: TLAExpression, rest: Ctx ?=> Compilation[Unit])(
                using Ctx,
            ): Compilation[Unit] =
              ctx.putConjunct(
                conj = renderTLAExpr(expr)
                  *> write(" = __value"),
                after = rest,
              )
          given Ctx = Ctx.Init
          mappingMacro.readBody.renderConjunction(dunderRestCall)
        }
        *> newLine
        *> newLine
        *> write(namePrefix)
        *> write("_write(__state0, self")
        *> indicesArgsDefns
        *> write(", __value, __rest(_)) ==")
        *> newLine
        *> indentHereOffset(offset = 2) {
          given Yielder with
            def apply(expr: TLAExpression, rest: Ctx ?=> Compilation[Unit])(
                using Ctx,
            ): Compilation[Unit] =
              renderPCalStatement(
                stmt = PCalAssignment(
                  List(
                    PCalAssignmentPair(
                      lhs = PCalAssignmentLhsExtension(MPCalDollarVariable()),
                      rhs = expr,
                    ),
                  ),
                ),
                rest = rest,
              )
          given Ctx = Ctx.Init
          mappingMacro.writeBody.renderConjunction(dunderRestCall)
        }

    val ((), lines) = compilation.perform()
    lines
