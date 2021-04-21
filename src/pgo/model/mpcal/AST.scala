package pgo.model.mpcal

import pgo.model.RefersTo.Renamer
import pgo.model.{Definition, DefinitionOne, RefersTo, Rewritable, SourceLocatable, Visitable}
import pgo.model.tla._
import pgo.model.pcal._
import pgo.util.IdMap

sealed abstract class MPCalNode extends Rewritable with Visitable with SourceLocatable {
  override def decorateLike(succ: this.type): this.type =
    super.decorateLike(succ.setSourceLocation(sourceLocation))
}

final case class MPCalRefExpr(name: TLAIdentifier, mappingCount: Int) extends MPCalNode with RefersTo[MPCalParam]
final case class MPCalValExpr(name: TLAIdentifier, mappingCount: Int) extends MPCalNode with RefersTo[MPCalParam]

final case class MPCalDollarValue() extends MPCalNode

final case class MPCalDollarVariable() extends MPCalNode

final case class MPCalYield(expr: TLAExpression) extends MPCalNode

final case class MPCalCall(target: TLAIdentifier, arguments: List[TLAExpression]) extends MPCalNode with RefersTo[MPCalProcedure]

sealed abstract class MPCalParam extends MPCalNode with DefinitionOne {
  def name: TLAIdentifier
  override def arity: Int = 0
  override def identifier: Definition.ScopeIdentifier = Definition.ScopeIdentifierName(name)
}
final case class MPCalRefParam(override val name: TLAIdentifier, mappingCount: Int) extends MPCalParam
final case class MPCalValParam(override val name: TLAIdentifier, mappingCount: Int) extends MPCalParam

final case class MPCalBlock(name: TLAIdentifier, units: List[TLAUnit], macros: List[PCalMacro], mpcalProcedures: List[MPCalProcedure],
                            mappingMacros: List[MPCalMappingMacro], archetypes: List[MPCalArchetype],
                            variables: List[PCalVariableDeclaration], instances: List[MPCalInstance],
                            pcalProcedures: List[PCalProcedure],
                            processes: Either[List[PCalStatement],List[PCalProcess]]) extends MPCalNode {
  override def mapChildren(fn: Any => Any): this.type = {
    val renamer = new Renamer[Rewritable]()
    val mappedName = fn(name)
    val mappedUnits = renamer.mapConserveRenamingAny(units, fn)
    // like in PCal AST, macros and procedures are mutually referential, so if one changes, we need to recompute references
    var mappedMacros = macros.mapConserve(renamer.captureRenamingAny(_, fn))
    var mappedPCalProcedures = pcalProcedures.mapConserve(renamer.captureRenamingAny(_, fn))
    var mappedMPCalProcedures = mpcalProcedures.mapConserve(renamer.captureRenamingAny(_, fn))
    if((mappedMacros ne macros) || (mappedPCalProcedures ne pcalProcedures) || (mappedMPCalProcedures ne mpcalProcedures)) {
      def duplicator[N <: Rewritable](n: N): N =
        n.rewrite() {
          case call @PCalCall(_, _) => call.shallowCopy()
          case macroCall @PCalMacroCall(_, _) => macroCall.shallowCopy()
          case mpcalCall @MPCalCall(_, _) => mpcalCall.shallowCopy()
        }
      mappedMacros = mappedMacros.mapConserve(renamer.captureRenaming(_, duplicator[PCalMacro]))
      mappedPCalProcedures = mappedPCalProcedures.mapConserve(renamer.captureRenaming(_, duplicator[PCalProcedure]))
      mappedMPCalProcedures = mappedMPCalProcedures.mapConserve(renamer.captureRenaming(_, duplicator[MPCalProcedure]))
      val macroMap = (macros.view zip mappedMacros).to(IdMap)
      val pcalProcMap = (pcalProcedures.view zip mappedPCalProcedures).to(IdMap)
      val mpcalProcMap = (mpcalProcedures.view zip mappedMPCalProcedures).to(IdMap)
      def referenceFixer[N <: Visitable](n: N): Unit =
        n.visit() {
          case call @PCalCall(_, _) => call.setRefersTo(pcalProcMap(call.refersTo))
          case macroCall @PCalMacroCall(_, _) => macroCall.setRefersTo(macroMap(macroCall.refersTo))
          case mpcalCall @MPCalCall(_, _) => mpcalCall.setRefersTo(mpcalProcMap(mpcalCall.refersTo))
        }
      mappedMacros.foreach(referenceFixer(_))
      mappedPCalProcedures.foreach(referenceFixer(_))
      mappedMPCalProcedures.foreach(referenceFixer(_))
    }
    val mappedMappingMacros = mappingMacros.mapConserve(renamer.captureRenamingAny(_, fn))
    val mappedArchetypes = archetypes.mapConserve(archetype => fn(renamer(archetype)).asInstanceOf[MPCalArchetype])
    val mappedVariables = renamer.mapConserveRenamingAny(variables, fn)
    val mappedInstances = instances.mapConserve(instance => fn(renamer(instance)).asInstanceOf[MPCalInstance])
    val mappedProcesses: Either[List[PCalStatement],List[PCalProcess]] = processes match {
      case Left(body) =>
        val mappedBody = body.mapConserve(stmt => fn(renamer(stmt)).asInstanceOf[PCalStatement])
        if(mappedBody ne body) {
          Left(mappedBody)
        } else processes
      case Right(processes) =>
        val mappedProcesses = processes.mapConserve(process => fn(renamer(process)).asInstanceOf[PCalProcess])
        if(mappedProcesses ne processes) {
          Right(mappedProcesses)
        } else this.processes
    }
    withChildren(Iterator(mappedName, mappedUnits, mappedMacros, mappedMPCalProcedures, mappedMappingMacros, mappedArchetypes,
      mappedVariables, mappedInstances, mappedPCalProcedures, mappedProcesses))
  }
}

final case class MPCalProcedure(name: TLAIdentifier, params: List[MPCalParam], variables: List[PCalPVariableDeclaration],
                                body: List[PCalStatement]) extends MPCalNode {
  override def mapChildren(fn: Any => Any): this.type = {
    val renamer = new Renamer[DefinitionOne with Rewritable]()
    val mappedName = fn(name)
    val mappedParams = renamer.mapConserveRenamingAny(params, fn)
    val mappedVariables = renamer.mapConserveRenamingAny(variables, fn)
    val mappedBody = body.mapConserve(stmt => fn(renamer(stmt)).asInstanceOf[PCalStatement])
    withChildren(Iterator(mappedName, mappedParams, mappedVariables, mappedBody))
  }
}

final case class MPCalMappingMacro(name: TLAIdentifier, readBody: List[PCalStatement], writeBody: List[PCalStatement],
                                   freeVars: List[TLADefiningIdentifier]) extends MPCalNode {
  override def mapChildren(fn: Any => Any): this.type = {
    val renamer = new Renamer[TLADefiningIdentifier]()
    val mappedName = fn(name)
    val mappedFreeVars = renamer.mapConserveRenamingAny(freeVars, fn)
    val mappedReadBody = readBody.mapConserve(stmt => fn(renamer(stmt)).asInstanceOf[PCalStatement])
    val mappedWriteBody = writeBody.mapConserve(stmt => fn(renamer(stmt)).asInstanceOf[PCalStatement])
    withChildren(Iterator(mappedName, mappedReadBody, mappedWriteBody, mappedFreeVars))
  }
}

final case class MPCalArchetype(name: TLAIdentifier, selfDecl: TLADefiningIdentifier, params: List[MPCalParam],
                                variables: List[PCalVariableDeclaration], body: List[PCalStatement]) extends MPCalNode {
  override def mapChildren(fn: Any => Any): this.type = {
    val renamer = new Renamer[DefinitionOne with Rewritable]()
    val mappedName = fn(name)
    val mappedSelf = renamer.captureRenamingAny(selfDecl, fn)
    val mappedParams = renamer.mapConserveRenamingAny(params, fn)
    val mappedVariables = renamer.mapConserveRenamingAny(variables, fn)
    val mappedBody = body.mapConserve(stmt => fn(renamer(stmt)).asInstanceOf[PCalStatement])
    withChildren(Iterator(mappedName, mappedSelf, mappedParams, mappedVariables, mappedBody))
  }
}

final case class MPCalInstance(selfDecl: PCalVariableDeclarationBound, fairness: PCalFairness,
                               archetypeName: TLAIdentifier, arguments: List[Either[MPCalParam,TLAExpression]],
                               mappings: List[MPCalMapping]) extends MPCalNode with RefersTo[MPCalArchetype]

final case class MPCalMapping(target: MPCalMappingTarget, mappingMacroIdentifier: TLAIdentifier) extends MPCalNode with RefersTo[MPCalMappingMacro]

final case class MPCalMappingTarget(position: Int, mappingCount: Int) extends MPCalNode
