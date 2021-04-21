package pgo.model.pcal

import pgo.model.RefersTo.Renamer
import pgo.model.{Definition, DefinitionOne, RefersTo, Rewritable, SourceLocatable, Visitable}
import pgo.model.tla._
import pgo.util.IdMap


sealed abstract class PCalNode extends Rewritable with Visitable with SourceLocatable {
  override def decorateLike(succ: this.type): this.type =
    super.decorateLike(succ.setSourceLocation(sourceLocation))
}

sealed abstract class PCalFairness
object PCalFairness {
  case object Unfair extends PCalFairness
  case object WeakFair extends PCalFairness
  case object StrongFair extends PCalFairness
}

final case class PCalDefaultInitValue() extends PCalNode

final case class PCalAlgorithm(fairness: PCalFairness, name: TLAIdentifier, variables: List[PCalVariableDeclaration],
                               units: List[TLAUnit], macros: List[PCalMacro], procedures: List[PCalProcedure],
                               processes: Either[List[PCalStatement],List[PCalProcess]]) extends PCalNode {
  override def mapChildren(fn: Any => Any): this.type = {
    val renamer = new Renamer[Rewritable]()
    val mappedName = fn(name)
    val mappedVariables = renamer.mapConserveRenamingAny(variables, fn)
    val mappedUnits = renamer.mapConserveRenamingAny(units, fn)
    var mappedMacros = macros.mapConserve(renamer.captureRenamingAny(_, fn))
    var mappedProcedures = procedures.mapConserve(renamer.captureRenamingAny(_, fn))
    // macros and procedures are mutually referential, so we have to apply any renamings using a special strategy
    if((mappedMacros ne macros) || (mappedProcedures ne procedures)) {
      def duplicator[N <: Rewritable](n: N): N =
        n.rewrite() {
          case call @PCalCall(_, _) => call.shallowCopy()
          case macroCall @PCalMacroCall(_, _) => macroCall.shallowCopy()
        }
      mappedMacros = mappedMacros.mapConserve(renamer.captureRenaming(_, duplicator[PCalMacro]))
      mappedProcedures = mappedProcedures.mapConserve(renamer.captureRenaming(_, duplicator[PCalProcedure]))
      val macroMap = (macros.view zip mappedMacros).to(IdMap)
      val procMap = (procedures.view zip mappedProcedures).to(IdMap)
      def referenceFixer[N <: Visitable](n: N): Unit =
        n.visit() {
          case call @PCalCall(_, _) => call.setRefersTo(procMap(call.refersTo))
          case macroCall @PCalMacroCall(_, _) => macroCall.setRefersTo(macroMap(macroCall.refersTo))
        }
      mappedMacros.foreach(referenceFixer(_))
      mappedProcedures.foreach(referenceFixer(_))
    }
    val mappedProcesses = processes match {
      case Left(body) =>
        val mappedBody = body.mapConserve(stmt => fn(renamer(stmt)).asInstanceOf[PCalStatement])
        if(mappedBody ne body) {
          Left(mappedBody)
        } else processes
      case Right(processes) =>
        val mappedProcesses = processes.mapConserve(process => fn(renamer(process)).asInstanceOf[PCalProcess])
        if(mappedProcesses ne processes) {
          Right(mappedProcesses)
        } else processes
    }
    withChildren(Iterator(fairness, mappedName, mappedVariables, mappedUnits, mappedMacros, mappedProcedures, mappedProcesses))
  }
}

final case class PCalPVariableDeclaration(name: TLAIdentifier, value: Option[TLAExpression]) extends PCalNode with DefinitionOne {
  override def arity: Int = 0
  override def identifier: Definition.ScopeIdentifier = Definition.ScopeIdentifierName(name)
}

sealed abstract class PCalVariableDeclaration extends PCalNode with DefinitionOne {
  def name: TLAIdentifier
  override def arity: Int = 0
  override def identifier: Definition.ScopeIdentifier = Definition.ScopeIdentifierName(name)
}

final case class PCalVariableDeclarationEmpty(name: TLAIdentifier) extends PCalVariableDeclaration

sealed abstract class PCalVariableDeclarationBound extends PCalVariableDeclaration
final case class PCalVariableDeclarationValue(name: TLAIdentifier, value: TLAExpression) extends PCalVariableDeclarationBound
final case class PCalVariableDeclarationSet(name: TLAIdentifier, set: TLAExpression) extends PCalVariableDeclarationBound

final case class PCalMacro(name: TLAIdentifier, params: List[TLADefiningIdentifier], body: List[PCalStatement],
                           freeVars: List[TLADefiningIdentifier]) extends PCalNode {
  override def mapChildren(fn: Any => Any): this.type = {
    val renamer = new Renamer[TLADefiningIdentifier]()
    val mappedName = fn(name)
    val mappedFreeVars = renamer.mapConserveRenamingAny(freeVars, fn)
    val mappedParams = renamer.mapConserveRenamingAny(params, fn)
    val mappedBody = body.mapConserve(stmt => fn(renamer(stmt)).asInstanceOf[PCalStatement])
    withChildren(Iterator(mappedName, mappedParams, mappedBody, mappedFreeVars))
  }
}

final case class PCalProcedure(name: TLAIdentifier, params: List[PCalPVariableDeclaration],
                               variables: List[PCalPVariableDeclaration], body: List[PCalStatement]) extends PCalNode {
  override def mapChildren(fn: Any => Any): this.type = {
    val renamer = new Renamer[DefinitionOne with Rewritable]()
    val mappedName = fn(name).asInstanceOf[TLAIdentifier]
    val mappedParams = renamer.mapConserveRenamingAny(params, fn)
    val mappedVariables = renamer.mapConserveRenamingAny(variables, fn)
    val mappedBody = body.mapConserve(stmt => fn(renamer(stmt)).asInstanceOf[PCalStatement])
    withChildren(Iterator(mappedName, mappedParams, mappedVariables, mappedBody))
  }
}

final case class PCalProcess(selfDecl: PCalVariableDeclarationBound, fairness: PCalFairness,
                             variables: List[PCalVariableDeclaration], body: List[PCalStatement]) extends PCalNode {
  override def mapChildren(fn: Any => Any): this.type = {
    val renamer = new Renamer[PCalVariableDeclaration]()
    val mappedSelfDecl = renamer.captureRenamingAny(selfDecl, fn)
    val mappedVariables = renamer.mapConserveRenamingAny(variables, fn)
    val mappedBody = body.mapConserve(stmt => fn(renamer(stmt)).asInstanceOf[PCalStatement])
    withChildren(Iterator(mappedSelfDecl, fairness, mappedVariables, mappedBody))
  }
}

sealed abstract class PCalStatement extends PCalNode

final case class PCalExtensionStatement(contents: Any) extends PCalStatement

final case class PCalAssert(condition: TLAExpression) extends PCalStatement

final case class PCalAssignment(pairs: List[PCalAssignmentPair]) extends PCalStatement

final case class PCalAssignmentPair(lhs: PCalAssignmentLhs, rhs: TLAExpression) extends PCalNode

sealed abstract class PCalAssignmentLhs extends PCalNode
final case class PCalAssignmentLhsIdentifier(identifier: TLAIdentifier) extends PCalAssignmentLhs with RefersTo[DefinitionOne]
final case class PCalAssignmentLhsProjection(lhs: PCalAssignmentLhs, projections: List[TLAExpression]) extends PCalAssignmentLhs
final case class PCalAssignmentLhsExtension(contents: Any) extends PCalAssignmentLhs

final case class PCalAwait(condition: TLAExpression) extends PCalStatement

final case class PCalCall(target: TLAIdentifier, arguments: List[TLAExpression]) extends PCalStatement with RefersTo[PCalProcedure]

final case class PCalEither(cases: List[List[PCalStatement]]) extends PCalStatement {
  require(cases.nonEmpty, s"either must have at least one case")
}

// target is a string, because it would be much to hard to integrate gotos (which can reference any local label) into RefersTo
final case class PCalGoto(target: String) extends PCalStatement

final case class PCalIf(condition: TLAExpression, yes: List[PCalStatement], no: List[PCalStatement]) extends PCalStatement

final case class PCalLabel(name: String, modifier: PCalLabel.Modifier) extends PCalNode
object PCalLabel {
  sealed abstract class Modifier
  case object PlusModifier extends Modifier
  case object MinusModifier extends Modifier
  case object NoModifier extends Modifier
}

final case class PCalLabeledStatements(label: PCalLabel, statements: List[PCalStatement]) extends PCalStatement

final case class PCalMacroCall(target: TLAIdentifier, arguments: List[TLAExpression]) extends PCalStatement with RefersTo[PCalMacro]

final case class PCalPrint(value: TLAExpression) extends PCalStatement

final case class PCalReturn() extends PCalStatement

final case class PCalSkip() extends PCalStatement

final case class PCalWhile(condition: TLAExpression, body: List[PCalStatement]) extends PCalStatement

final case class PCalWith(variables: List[PCalVariableDeclarationBound], body: List[PCalStatement]) extends PCalStatement {
  override def mapChildren(fn: Any => Any): this.type = {
    val renamer = new Renamer[PCalVariableDeclarationBound]()
    val mappedVariables = renamer.mapConserveRenamingAny(variables, fn)
    val mappedBody = body.mapConserve(bodyStmt => fn(renamer(bodyStmt)).asInstanceOf[PCalStatement])
    withChildren(Iterator(mappedVariables, mappedBody))
  }
}
