package pgo.trans

import pgo.model.{DefinitionOne, PGoError, SourceLocatable, SourceLocation, Visitable}
import pgo.model.mpcal._
import pgo.model.pcal._
import pgo.model.tla._
import pgo.util.{Description, IdMap, IdSet, MPCalPassUtils}

import Description._

import scala.annotation.tailrec
import scala.collection.mutable

object MPCalSemanticCheckPass {

  final case class SemanticError(override val errors: List[SemanticError.Error]) extends PGoError

  object SemanticError {
    sealed abstract class Error(override val sourceLocation: SourceLocation, override val description: Description) extends PGoError.Error

    final case class LabelRequiredError(node: SourceLocatable) extends Error(
      node.sourceLocation, d"label required")

    final case class LabelForbiddenError(node: SourceLocatable) extends Error(
      node.sourceLocation, d"label forbidden")

    final case class ReservedLabelError(node: SourceLocatable) extends Error(
      node.sourceLocation, d"label name is reserved (reserved names are `Done` and `Error`)")

    final case class MultipleAssignmentError(node1: SourceLocatable, node2: SourceLocatable) extends Error(
      node2.sourceLocation, d"multiple assignment within same label.\ninitial assignment at ${
        node1.sourceLocation.longDescription
      }\nconflicts with other assignment")

    final case class LabelNotDefinedError(node: SourceLocatable) extends Error(
      node.sourceLocation, d"label not defined")

    final case class RecursiveMacroError(node: SourceLocatable) extends Error(
      node.sourceLocation, d"macro call leads to recursion")

    final case class MPCalKindMismatchError(usage: SourceLocatable, defn: SourceLocatable) extends Error(
      usage.sourceLocation, d"reference to kinded definition at ${
        defn.sourceLocation.longDescription
      }\n does not match")
  }

  @throws[PGoError]
  def apply(tlaModule: TLAModule, mpcalBlock: MPCalBlock): Unit = {
    val errors = mutable.ListBuffer[SemanticError.Error]()

    // enforce that the first statement / top-level statements in:
    // - procedures
    // - archetypes
    // - processes
    // must be labeled
    locally {
      def checkInBody(body: List[PCalStatement]): Unit = {
        body.foreach {
          case PCalLabeledStatements(_, _) => // ok
          case stmt =>
            errors += SemanticError.LabelRequiredError(stmt)
        }
      }
      mpcalBlock.visit(Visitable.TopDownFirstStrategy) {
        case MPCalArchetype(_, _, _, _, body) => checkInBody(body)
        case MPCalProcedure(_, _, _, body) => checkInBody(body)
        case PCalProcedure(_, _, _, body) => checkInBody(body)
        case PCalProcess(_, _, _, body) => checkInBody(body)
      }
    }

    // enforce cases where no labels may be present
    locally {
      def requireNoLabels(visitable: Visitable): Unit =
        visitable.visit(Visitable.TopDownFirstStrategy) {
          case PCalLabeledStatements(label, _) =>
            errors += SemanticError.LabelForbiddenError(label)
        }

      mpcalBlock.visit(Visitable.TopDownFirstStrategy) {
        case m: PCalMacro => requireNoLabels(m)
        case mm: MPCalMappingMacro => requireNoLabels(mm)
        case w: PCalWith => requireNoLabels(w)
      }
    }

    // enforce reserved label names
    mpcalBlock.visit(Visitable.BottomUpFirstStrategy) {
      case PCalLabeledStatements(label, _) if label.name == "Error" || label.name == "Done" =>
        errors += SemanticError.ReservedLabelError(label)
    }

    // enforce non-recursive macros
    val hasRecursiveMacro: Boolean = locally {
      var hasRecursiveMacro = false
      def checkNonRec(visitable: Visitable, macrosBeingExpanded: Map[String,PCalMacroCall]): Unit =
        visitable.visit(Visitable.TopDownFirstStrategy) {
          case innerCall @PCalMacroCall(target, _) =>
            macrosBeingExpanded.get(target.id) match {
              case Some(outerCall) =>
                hasRecursiveMacro = true
                errors += SemanticError.RecursiveMacroError(outerCall)
              case None =>
                val updatedExpansion = macrosBeingExpanded
                  .updated(target.id, macrosBeingExpanded.getOrElse(target.id, innerCall))
                innerCall.refersTo.body.foreach(checkNonRec(_, updatedExpansion))
            }
        }

      checkNonRec(mpcalBlock, Map.empty)
      hasRecursiveMacro
    }

    val containsLabels: IdSet[PCalStatement] = locally {
      var containsLabels = IdSet.empty[PCalStatement]
      def gatherContainsLabels(stmt: PCalStatement): Boolean = {
        // note: the seemingly over-engineered map+reduce ensures all sub-statements are reached,
        //   vs. a more concise but short-circuiting .exists(...)
        val result: Boolean = stmt match {
          case PCalEither(cases) => cases.view.flatMap(_.view.map(gatherContainsLabels)).foldLeft(false)(_ || _)
          case PCalIf(_, yes, no) =>
            yes.view.map(gatherContainsLabels).foldLeft(false)(_ || _) ||
              no.view.map(gatherContainsLabels).foldLeft(false)(_ || _)
          case PCalLabeledStatements(_, statements) =>
            statements.foreach(gatherContainsLabels)
            true
          case PCalWhile(_, body) => body.view.map(gatherContainsLabels).foldLeft(false)(_ || _)
          case PCalWith(_, body) => body.view.map(gatherContainsLabels).foldLeft(false)(_ || _)
          case _ => false
        }
        if(result) {
          containsLabels += stmt
        }
        result
      }

      mpcalBlock.visit(Visitable.TopDownFirstStrategy) {
        case stmt: PCalStatement => gatherContainsLabels(stmt)
      }

      containsLabels
    }

    val tailStatements: IdMap[PCalStatement,Vector[PCalStatement]] = locally {
      var tailStatements = IdMap.empty[PCalStatement,Vector[PCalStatement]]

      def gatherTailStatements(stmt: PCalStatement): Vector[PCalStatement] = {
        val result: Vector[PCalStatement] = stmt +: (stmt match {
          case PCalEither(cases) =>
            cases.view.map(_.view.map(gatherTailStatements).last)
              .foldLeft(Vector.empty[PCalStatement])(_ ++ _)
          case PCalIf(_, yes, no) =>
            yes.view.map(gatherTailStatements).last ++
              no.view.map(gatherTailStatements).lastOption.getOrElse(Vector.empty)
          case PCalLabeledStatements(_, statements) =>
            statements.view.map(gatherTailStatements).last
          case macroCall @PCalMacroCall(_, _) if !hasRecursiveMacro =>
            macroCall.refersTo.body.view.map(gatherTailStatements).lastOption.getOrElse(Vector.empty)
          case PCalWhile(_, body) =>
            body.view.map(gatherTailStatements).lastOption.getOrElse(Vector.empty)
          case PCalWith(_, body) =>
            body.view.map(gatherTailStatements).lastOption.getOrElse(Vector.empty)
          case _ => Vector.empty
        })
        tailStatements = tailStatements.updated(stmt, result)
        result
      }

      mpcalBlock.visit(Visitable.TopDownFirstStrategy) {
        case stmt: PCalStatement =>
          gatherTailStatements(stmt)
      }
      tailStatements
    }

    def checkWhileLabelPlacement(visitable: Visitable): Unit =
      visitable.visit(Visitable.TopDownFirstStrategy) {
        case PCalLabeledStatements(_, PCalWhile(_, whileBody) :: restBody) =>
          whileBody.foreach(checkWhileLabelPlacement)
          restBody.foreach(checkWhileLabelPlacement)
        case stmt @PCalWhile(_, body) =>
          errors += SemanticError.LabelRequiredError(stmt)
          body.foreach(checkWhileLabelPlacement)
      }

    checkWhileLabelPlacement(mpcalBlock)

    // check whether statements that must be followed by a label are followed by a label
    locally {
      def supportsTailCall(stmt: PCalStatement): Boolean =
        stmt match {
          case _: PCalGoto => true
          case _: PCalReturn => true
          case _ => false
        }

      def checkInBody(body: List[PCalStatement]): Unit =
        if(body.size > 1) {
          (body.view zip body.tail.view).foreach {
            case (_, PCalLabeledStatements(_, _)) => // pass
            case (beforeStmt, notLabel) =>

              val labelNeedingStatementComesBefore =
                tailStatements(beforeStmt).exists {
                  case ifStmt: PCalIf => containsLabels(ifStmt)
                  case _: PCalReturn => true
                  case _: PCalGoto => true
                  case _: PCalCall => !supportsTailCall(notLabel)
                  case PCalExtensionStatement(_: MPCalCall) => !supportsTailCall(notLabel)
                  case _ => false
                }
              if (labelNeedingStatementComesBefore) {
                errors += SemanticError.LabelRequiredError(notLabel)
              }
          }
        }

      // visit all parts of the MPCal block that contain a list of statements
      mpcalBlock.visit(Visitable.BottomUpFirstStrategy) {
        case MPCalMappingMacro(_, readBody, writeBody, _) =>
          checkInBody(readBody)
          checkInBody(writeBody)
        case PCalMacro(_, _, body, _) => checkInBody(body)
        case PCalProcedure(_, _, _, body) => checkInBody(body)
        case MPCalProcedure(_, _, _, body) => checkInBody(body)
        case PCalProcess(_, _, _, body) => checkInBody(body)
        case MPCalArchetype(_, _, _, _, body) => checkInBody(body)

        case PCalLabeledStatements(_, body) => checkInBody(body)
        case PCalWhile(_, body) => checkInBody(body)
        case PCalIf(_, yes, no) =>
          checkInBody(yes)
          checkInBody(no)
        case PCalEither(cases) =>
          cases.foreach(checkInBody)
        case PCalWith(_, body) => checkInBody(body)
      }
    }

    // enforce multiple assignment rules
    locally {
      def checkInBody(assignedVars: Map[TLAIdentifier,TLAIdentifier], contextualBindings: Map[String,DefinitionOne], body: List[PCalStatement]): Map[TLAIdentifier,TLAIdentifier] =
        body.view.scanLeft(assignedVars) { (assignedVars, stmt) =>
          stmt match {
            case PCalAssignment(pairs) =>
              pairs.view.scanLeft(assignedVars) { (assignedVars, pair) =>
                val PCalAssignmentPair(lhs, _) = pair
                @tailrec
                def getId(lhs: PCalAssignmentLhs): TLAIdentifier =
                  lhs match {
                    case PCalAssignmentLhsIdentifier(identifier) => identifier
                    case PCalAssignmentLhsProjection(lhs, _) => getId(lhs)
                  }

                val lhsId = getId(lhs)
                assignedVars.get(lhsId) match {
                  case Some(conflictingId) =>
                    errors += SemanticError.MultipleAssignmentError(conflictingId, lhsId)
                  case None => // pass
                }
                assignedVars.updated(lhsId, lhsId)
              }.last
            case PCalEither(cases) =>
              cases.map(checkInBody(assignedVars, contextualBindings, _)).reduce(_ ++ _)
            case PCalIf(_, yes, no) =>
              checkInBody(assignedVars, contextualBindings, yes) ++ checkInBody(assignedVars, contextualBindings, no)
            case PCalLabeledStatements(_, statements) =>
              checkInBody(Map.empty, contextualBindings, statements)
              Map.empty
            case macroCall: PCalMacroCall if !hasRecursiveMacro =>
              checkInBody(
                assignedVars,
                contextualBindings,
                MPCalPassUtils.expandMacroCalls(List(macroCall), contextualBindings))
            case PCalWhile(_, body) => checkInBody(assignedVars, contextualBindings, body)
            case PCalWith(bindings, body) =>
              checkInBody(
                assignedVars,
                bindings.foldLeft(contextualBindings)((contextualBindings, b) => contextualBindings.updated(b.name.id, b)),
                body)
            case _ => assignedVars
          }
        }.last

      MPCalPassUtils.forEachBody(mpcalBlock)((body, contextualBindings) => checkInBody(Map.empty, contextualBindings, body))
    }

    // for each PCal "body", every goto must refer to a defined label
    locally {
      def checkInBody(body: List[PCalStatement]): Unit = {
        val labels = mutable.HashSet[String]()
        body.foreach(_.visit(Visitable.BottomUpFirstStrategy) {
          case PCalLabeledStatements(label, _) => labels += label.name
        })
        body.foreach(_.visit(Visitable.BottomUpFirstStrategy) {
          case stmt @PCalGoto(label) if !labels(label) =>
            errors += SemanticError.LabelNotDefinedError(stmt)
        })
      }

      MPCalPassUtils.forEachBody(mpcalBlock)((body, _) => checkInBody(body))
    }

    // enforce kind-matching for MPCal params (ref vs. non-ref, number of mappings)
    locally {
      def checkMPCalParamRefs(body: List[PCalStatement], params: List[MPCalParam]): Unit = {
        val paramsMap = params.view.map(p => p -> p).to(IdMap)
        body.foreach { stmt =>
          stmt.visit(Visitable.BottomUpFirstStrategy) {
            case ref @MPCalValExpr(_, mappingCount) =>
              paramsMap(ref.refersTo) match {
                case defn @ MPCalRefParam(_, mappingCountP) =>
                  if(mappingCountP > mappingCount) {
                    errors += SemanticError.MPCalKindMismatchError(usage = ref, defn = defn)
                  }
                case defn @MPCalValParam(_, mappingCountP) =>
                  if(mappingCountP > mappingCount) {
                    errors += SemanticError.MPCalKindMismatchError(usage = ref, defn = defn)
                  }
              }
            case ref @MPCalRefExpr(_, mappingCount) =>
              paramsMap(ref.refersTo) match {
                case defn @ MPCalRefParam(_, mappingCountP) =>
                  if(mappingCountP > mappingCount) {
                    errors += SemanticError.MPCalKindMismatchError(usage = ref, defn = defn)
                  }
                case defn @MPCalValParam(_, _) =>
                  errors += SemanticError.MPCalKindMismatchError(usage = ref, defn = defn)
              }
          }
        }
      }

      mpcalBlock.visit(Visitable.TopDownFirstStrategy) {
        case MPCalArchetype(_, _, params, _, body) =>
          checkMPCalParamRefs(body, params)
        case MPCalProcedure(_, params, _, body) =>
          checkMPCalParamRefs(body, params)
        case instance @MPCalInstance(_, _, _, arguments, mappings) =>
          val archetype = instance.refersTo
          mappings.foreach {
            case MPCalMapping(target @MPCalMappingTarget(position, mappingCount), id) =>
              arguments(position) match {
                case Left(param) => param match {
                  case MPCalRefParam(_, mappingCountP) =>
                    if(mappingCount < mappingCountP) {
                      errors += SemanticError.MPCalKindMismatchError(usage = target, defn = param)
                    }
                  case MPCalValParam(_, mappingCountP) =>
                    if(mappingCount < mappingCountP) {
                      errors += SemanticError.MPCalKindMismatchError(usage = target, defn = param)
                    }
                }
                case Right(_) => // any mappings work here, we'll add an underlying variable if we have to; TODO: is this true?
              }
          }
          (archetype.params.view zip arguments.view).foreach {
            case (MPCalRefParam(_, mappingCountP), Left(MPCalRefParam(_, mappingCount))) if mappingCount == mappingCountP => // ok
            case (MPCalValParam(_, 0), Right(_)) => // ok
            case (MPCalValParam(_, mappingCountP), Left(MPCalValParam(_, mappingCount))) if mappingCount == mappingCountP => // ok
            case (param, Left(arg)) =>
              errors += SemanticError.MPCalKindMismatchError(usage = arg, defn = param)
            case (param, Right(arg)) =>
              errors += SemanticError.MPCalKindMismatchError(usage = arg, defn = param)
          }
      }
    }

    if(errors.nonEmpty) {
      throw SemanticError(errors.result())
    }
  }
}
