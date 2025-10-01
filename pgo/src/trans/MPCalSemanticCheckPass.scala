package pgo.trans

import scala.annotation.tailrec
import scala.collection.mutable

import pgo.model.mpcal.*
import pgo.model.pcal.*
import pgo.model.tla.*
import pgo.model.{
  DefinitionOne,
  PGoError,
  RefersTo,
  SourceLocatable,
  SourceLocation,
  Visitable,
}
import pgo.trans.MPCalSemanticCheckPass.SemanticError.PCalInvalidAssignment
import pgo.util.{!!!, ById, Description, MPCalPassUtils}

import Description.*

object MPCalSemanticCheckPass {

  final case class SemanticError(override val errors: List[SemanticError.Error])
      extends PGoError

  object SemanticError {
    sealed abstract class Error(
        override val sourceLocation: SourceLocation,
        override val description: Description,
    ) extends PGoError.Error

    final case class LabelRequiredError(node: SourceLocatable)
        extends Error(node.sourceLocation, d"label required")

    final case class LabelForbiddenError(node: SourceLocatable)
        extends Error(node.sourceLocation, d"label forbidden")

    final case class ReservedLabelError(node: SourceLocatable)
        extends Error(
          node.sourceLocation,
          d"label name is reserved (reserved names are `Done` and `Error`)",
        )

    final case class MultipleAssignmentError(
        node1: SourceLocatable,
        node2: SourceLocatable,
    ) extends Error(
          node2.sourceLocation,
          d"multiple assignment within same label.\ninitial assignment at ${node1.sourceLocation.longDescription}\nconflicts with other assignment",
        )

    final case class LabelNotDefinedError(node: SourceLocatable)
        extends Error(node.sourceLocation, d"label not defined")

    final case class RecursiveMacroError(node: SourceLocatable)
        extends Error(node.sourceLocation, d"macro call leads to recursion")

    final case class MPCalKindMismatchError(
        usage: SourceLocatable,
        defn: SourceLocatable,
    ) extends Error(
          usage.sourceLocation,
          d"reference to kinded definition at ${defn.sourceLocation.longDescription}\n does not match",
        )

    final case class MPCalMappingValueRefMismatchError(
        usage: SourceLocatable,
        defn: SourceLocatable,
    ) extends Error(
          usage.sourceLocation,
          d"non-ref archetype parameter defined at ${defn.sourceLocation.longDescription}\n should not have a mapping",
        )

    final case class MPCalReadWriteAssignmentForbidden(
        usage: SourceLocatable,
        defn: SourceLocatable,
    ) extends Error(
          usage.sourceLocation,
          d"assignment implies both a read from and a write to the state variable defined at ${defn.sourceLocation.longDescription}\n if this is intended, use a with statement to explicitly show the separate read and write operations",
        )

    final case class PClArityMismatch(
        usage: SourceLocatable,
        defn: SourceLocatable,
    ) extends Error(
          usage.sourceLocation,
          d"call arity at ${defn.sourceLocation.longDescription}\n does not match",
        )

    final case class MPCalMultipleMapping(
        firstMapping: SourceLocatable,
        secondMapping: SourceLocatable,
    ) extends Error(
          secondMapping.sourceLocation,
          d"instance parameter mapped at ${firstMapping.sourceLocation.longDescription}\n is mapped again",
        )

    final case class ConsistencyCheckFailed(error: PGoError.Error)
        extends Error(
          error.sourceLocation,
          d"semantic check on output failed. probably a PGo bug!\n${error.description.indented}",
        )

    final case class PCalInvalidAssignment(occurrence: SourceLocatable)
        extends Error(
          occurrence.sourceLocation,
          d"invalid assignment: assigned to something that isn't a state variable",
        )
  }

  @throws[PGoError]
  def apply(
      tlaModule: TLAModule,
      mpcalBlock: MPCalBlock,
      noMultipleWrites: Boolean,
  ): Unit = {
    val errors = mutable.ListBuffer[SemanticError.Error]()
    var block = mpcalBlock

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
      block.visit(Visitable.TopDownFirstStrategy) {
        case MPCalArchetype(_, _, _, _, body) => checkInBody(body)
        case MPCalProcedure(_, _, _, _, body) => checkInBody(body)
        case PCalProcedure(_, _, _, _, body)  => checkInBody(body)
        case PCalProcess(_, _, _, body)       => checkInBody(body)
      }
    }

    // enforce cases where no labels may be present
    locally {
      def requireNoLabels(visitable: Visitable): Unit =
        visitable.visit(Visitable.TopDownFirstStrategy) {
          case PCalLabeledStatements(label, _) =>
            errors += SemanticError.LabelForbiddenError(label)
        }

      block.visit(Visitable.TopDownFirstStrategy) {
        case m: PCalMacro          => requireNoLabels(m)
        case mm: MPCalMappingMacro => requireNoLabels(mm)
        case w: PCalWith           => requireNoLabels(w)
      }
    }

    // enforce reserved label names
    block.visit(Visitable.BottomUpFirstStrategy) {
      case PCalLabeledStatements(label, _)
          if label.name == "Error" || label.name == "Done" =>
        errors += SemanticError.ReservedLabelError(label)
    }

    // enforce non-recursive macros
    block = locally {
      var hasRecursiveMacro = false
      def checkNonRec(
          visitable: Visitable,
          macrosBeingExpanded: Map[String, PCalMacroCall],
      ): Unit =
        visitable.visit(Visitable.TopDownFirstStrategy) {
          case innerCall @ PCalMacroCall(target, _) =>
            macrosBeingExpanded.get(target.id) match {
              case Some(outerCall) =>
                hasRecursiveMacro = true
                errors += SemanticError.RecursiveMacroError(outerCall)
              case None =>
                val updatedExpansion = macrosBeingExpanded
                  .updated(
                    target.id,
                    macrosBeingExpanded.getOrElse(target.id, innerCall),
                  )
                innerCall.refersTo.body.foreach(
                  checkNonRec(_, updatedExpansion),
                )
            }
        }

      checkNonRec(block, Map.empty)

      if (!hasRecursiveMacro) {
        MPCalPassUtils.rewriteEachBody(block) { (body, lexicalScope) =>
          MPCalPassUtils.expandMacroCalls(body, lexicalScope)
        }
      } else {
        block
      }
    }

    // !!!! beyond this point, macros will already be expanded if possible, and their contents may be ignored !!!!

    val containsLabels: Set[ById[PCalStatement]] =
      MPCalPassUtils.gatherContainsLabels(block)

    val tailStatements: Map[ById[PCalStatement], Vector[PCalStatement]] =
      locally {
        var tailStatements =
          Map.empty[ById[PCalStatement], Vector[PCalStatement]]

        def gatherTailStatements(stmt: PCalStatement): Vector[PCalStatement] = {
          val result: Vector[PCalStatement] = stmt +: (stmt match {
            case PCalEither(cases) =>
              cases.view
                .map(_.view.map(gatherTailStatements).last)
                .foldLeft(Vector.empty[PCalStatement])(_ ++ _)
            case PCalIf(_, yes, no) =>
              yes.view.map(gatherTailStatements).last ++
                no.view
                  .map(gatherTailStatements)
                  .lastOption
                  .getOrElse(Vector.empty)
            case PCalLabeledStatements(_, statements) =>
              statements.view.map(gatherTailStatements).last
            case PCalWhile(_, body) =>
              body.view
                .map(gatherTailStatements)
                .lastOption
                .getOrElse(Vector.empty)
            case PCalWith(_, body) =>
              body.view
                .map(gatherTailStatements)
                .lastOption
                .getOrElse(Vector.empty)
            case _ => Vector.empty
          })
          tailStatements = tailStatements.updated(ById(stmt), result)
          result
        }

        block.visit(Visitable.TopDownFirstStrategy) {
          case stmt: PCalStatement =>
            gatherTailStatements(stmt)
        }
        tailStatements
      }

    def checkWhileLabelPlacement(visitable: Visitable): Unit =
      visitable.visit(Visitable.TopDownFirstStrategy) {
        case PCalMacro(
              _,
              _,
              _,
              _,
            ) => // skip macro bodies, we check these at expansion site
        case PCalLabeledStatements(_, PCalWhile(_, whileBody) :: restBody) =>
          whileBody.foreach(checkWhileLabelPlacement)
          restBody.foreach(checkWhileLabelPlacement)
        case stmt @ PCalWhile(_, body) =>
          errors += SemanticError.LabelRequiredError(stmt)
          body.foreach(checkWhileLabelPlacement)
      }

    // check that all while statements are directly inside labels (accounting for macro expansion, if that's sound)
    checkWhileLabelPlacement(block)

    // check whether statements that must be followed by a label are followed by a label
    locally {
      def supportsTailCall(stmt: PCalStatement): Boolean =
        stmt match {
          case _: PCalGoto   => true
          case _: PCalReturn => true
          case _             => false
        }

      def checkInBody(body: List[PCalStatement]): Unit =
        if (body.size > 1) {
          (body.view zip body.tail.view).foreach {
            case (_, PCalLabeledStatements(_, _)) => // pass
            case (beforeStmt, notLabel) =>
              val labelNeedingStatementComesBefore =
                tailStatements(ById(beforeStmt)).exists {
                  case ifStmt: PCalIf => containsLabels(ById(ifStmt))
                  case eitherStmt: PCalEither =>
                    containsLabels(ById(eitherStmt))
                  case _: PCalReturn => true
                  case _: PCalGoto   => true
                  case _: PCalCall   => !supportsTailCall(notLabel)
                  case PCalExtensionStatement(_: MPCalCall) =>
                    !supportsTailCall(notLabel)
                  case _ => false
                }
              if (labelNeedingStatementComesBefore) {
                errors += SemanticError.LabelRequiredError(notLabel)
              }
          }
        }

      // visit all parts of the MPCal block that contain a list of statements
      block.visit(Visitable.BottomUpFirstStrategy) {
        case MPCalMappingMacro(_, _, readBody, writeBody) =>
          checkInBody(readBody)
          checkInBody(writeBody)
        case PCalMacro(_, _, body, _)         => checkInBody(body)
        case PCalProcedure(_, _, _, _, body)  => checkInBody(body)
        case MPCalProcedure(_, _, _, _, body) => checkInBody(body)
        case PCalProcess(_, _, _, body)       => checkInBody(body)
        case MPCalArchetype(_, _, _, _, body) => checkInBody(body)

        case PCalLabeledStatements(_, body) => checkInBody(body)
        case PCalWhile(_, body)             => checkInBody(body)
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
      def checkInBody(
          assignedVars: Map[TLAIdentifier, TLAIdentifier],
          body: List[PCalStatement],
      ): Map[TLAIdentifier, TLAIdentifier] =
        body.view
          .scanLeft(assignedVars) { (assignedVars, stmt) =>
            stmt match {
              case PCalAssignment(pairs) =>
                pairs.view
                  .scanLeft(assignedVars) { (assignedVars, pair) =>
                    val PCalAssignmentPair(lhs, _) = pair
                    @tailrec
                    def getId(lhs: PCalAssignmentLhs): TLAIdentifier =
                      lhs match {
                        case PCalAssignmentLhsIdentifier(identifier) =>
                          identifier
                        case PCalAssignmentLhsProjection(lhs, _) => getId(lhs)
                        case PCalAssignmentLhsExtension(
                              MPCalDollarVariable(),
                            ) =>
                          TLAIdentifier(
                            "$variable",
                          ) // hack to model special var
                        case PCalAssignmentLhsExtension(_) => !!!
                      }

                    val lhsId = getId(lhs)
                    assignedVars.get(lhsId) match {
                      case Some(conflictingId) =>
                        errors += SemanticError.MultipleAssignmentError(
                          conflictingId,
                          lhsId,
                        )
                      case None => // pass
                    }
                    assignedVars.updated(lhsId, lhsId)
                  }
                  .last
              case PCalEither(cases) =>
                cases.map(checkInBody(assignedVars, _)).reduce(_ ++ _)
              case PCalIf(_, yes, no) =>
                checkInBody(assignedVars, yes) ++ checkInBody(assignedVars, no)
              case PCalLabeledStatements(_, statements) =>
                checkInBody(Map.empty, statements)
                Map.empty
              case PCalWhile(_, body) => checkInBody(assignedVars, body)
              case PCalWith(bindings, body) =>
                checkInBody(assignedVars, body)
              case _ => assignedVars
            }
          }
          .last

      if (noMultipleWrites) {
        MPCalPassUtils.forEachBody(block)((body, _) =>
          checkInBody(Map.empty, body),
        )
      }
    }

    // for each PCal "body", every goto must refer to a defined label
    locally {
      def checkInBody(body: List[PCalStatement]): Unit = {
        val labels = mutable.HashSet[String]("Error", "Done")
        body.foreach(_.visit(Visitable.BottomUpFirstStrategy) {
          case PCalLabeledStatements(label, _) => labels += label.name
        })
        body.foreach(_.visit(Visitable.BottomUpFirstStrategy) {
          case stmt @ PCalGoto(label) if !labels(label) =>
            errors += SemanticError.LabelNotDefinedError(stmt)
        })
      }

      // macros may reference labels that only make sense at expansion site, so we shouldn't naively check unexpanded macros
      // macros are already expanded here, so just checking the expansion is good enough, and we can just ignore macro defs
      MPCalPassUtils.forEachBody(block, ignoreMacros = true)((body, _) =>
        checkInBody(body),
      )
    }

    // for each PCal procedure call, the argument count must match parameter count at the definition
    locally {
      block.visit(Visitable.TopDownFirstStrategy) {
        case call @ PCalCall(_, arguments) =>
          if (call.refersTo.params.size != arguments.size) {
            errors += SemanticError.PClArityMismatch(
              usage = call,
              defn = call.refersTo,
            )
          }
      }
    }

    // enforce kind-matching for MPCal params (ref vs. non-ref, number of mappings)
    locally {
      def checkMPCalParamRefs(
          body: List[PCalStatement],
          params: List[MPCalParam],
      ): Unit = {
        val paramsMap =
          params.view.map(p => (p: DefinitionOne) -> p).to(ById.mapFactory)
        body.foreach { stmt =>
          lazy val impl: PartialFunction[Visitable, Unit] = {
            case PCalAssignmentPair(lhs, rhs) =>
              // make sure to actually process assignment RHS
              rhs.visit(Visitable.TopDownFirstStrategy)(impl)

              @tailrec
              def findMappingCount(lhs: PCalAssignmentLhs, acc: Int = 0): Int =
                lhs match {
                  case PCalAssignmentLhsIdentifier(_) => acc
                  case PCalAssignmentLhsProjection(lhs, _) =>
                    findMappingCount(lhs, acc + 1)
                  case PCalAssignmentLhsExtension(_) => !!!
                }

              @tailrec
              def findDefn(lhs: PCalAssignmentLhs): Option[MPCalRefParam] =
                lhs match {
                  case lhs @ PCalAssignmentLhsIdentifier(_) =>
                    lhs.refersTo match {
                      case p: MPCalRefParam => Some(p)
                      case _                => None
                    }
                  case PCalAssignmentLhsProjection(lhs, _) => findDefn(lhs)
                  case PCalAssignmentLhsExtension(_)       => !!!
                }

              findDefn(lhs).foreach { defn =>
                val mappingCount = findMappingCount(lhs)
                val mappingCountP = defn.mappingCount
                // the mapping count must match exactly:
                // - too few, and there is no reasonable behaviour
                // - too many, and it implies a combined read-write, which would be confusing
                if (mappingCountP != mappingCount) {
                  if (mappingCountP < mappingCount) {
                    errors += SemanticError.MPCalReadWriteAssignmentForbidden(
                      usage = lhs,
                      defn = defn,
                    )
                  } else {
                    errors += SemanticError.MPCalKindMismatchError(
                      usage = lhs,
                      defn = defn,
                    )
                  }
                }
              }
            case ref @ MPCalRefExpr(_, mappingCount) =>
              paramsMap
                .get(ById(ref.refersTo))
                .map {
                  case defn @ MPCalRefParam(_, mappingCountP) =>
                    if (mappingCountP > mappingCount) {
                      errors += SemanticError.MPCalKindMismatchError(
                        usage = ref,
                        defn = defn,
                      )
                    }
                  case _: MPCalValParam => // pass; always OK
                }
                .getOrElse {
                  ref.refersTo match {
                    case PCalPVariableDeclaration(_, _) |
                        _: PCalVariableDeclaration =>
                    // OK, because it's either a state variable, or it's a local
                    case defn: SourceLocatable =>
                      errors += SemanticError.MPCalKindMismatchError(
                        usage = ref,
                        defn = defn,
                      )
                    case _ => !!! // all defns should be SourceLocatable
                  }
                }
            case expr @ MPCalPassUtils.MappedRead(mappingCount, ident)
                if (paramsMap.get(ById(ident.refersTo)) match {
                  case Some(MPCalRefParam(_, mappingCountP)) =>
                    mappingCount >= mappingCountP
                  case Some(MPCalValParam(_)) =>
                    true // it's a value, anything goes
                  case _ => false
                }) =>
              // if this is reached, we found an appropriate expression-level usage of a function-mapped param.
              // however, we may have missed issues in argument-position for the involved function applications
              // so we explicitly recurse over the arguments, knowing our expression can only be function applications
              // and idents
              @tailrec
              def checkMappingArgs(expr: TLAExpression): Unit =
                expr match {
                  case TLAGeneralIdentifier(_, Nil) =>
                  case TLAFunctionCall(function, params) =>
                    params.foreach(
                      _.visit(Visitable.TopDownFirstStrategy)(impl),
                    )
                    checkMappingArgs(function)
                  case _ => !!! // exhaustivity via MappedRead
                }

              checkMappingArgs(expr)
            case ref: (RefersTo[DefinitionOne @unchecked] & SourceLocatable)
                if ref.refersTo.isInstanceOf[DefinitionOne] && paramsMap
                  .contains(ById(ref.refersTo)) =>
              errors += SemanticError.MPCalKindMismatchError(
                usage = ref,
                defn = paramsMap(ById(ref.refersTo)),
              )
          }

          stmt.visit(Visitable.TopDownFirstStrategy)(impl)
        }
      }

      block.visit(Visitable.TopDownFirstStrategy) {
        case MPCalArchetype(_, _, params, _, body) =>
          checkMPCalParamRefs(body, params)
        case MPCalProcedure(_, _, params, _, body) =>
          checkMPCalParamRefs(body, params)
        case instance @ MPCalInstance(_, _, _, arguments, mappings) =>
          val archetype = instance.refersTo
          mappings.foreach {
            case MPCalMapping(
                  target @ MPCalMappingTarget(position, mappingCount),
                  _,
                ) =>
              arguments(position) match {
                case Left(param @ MPCalRefExpr(_, mappingCountP)) =>
                  if (mappingCount != mappingCountP) {
                    errors += SemanticError.MPCalKindMismatchError(
                      usage = target,
                      defn = param,
                    )
                  }
                case Right(_) =>
                  // _almost_ any mappings work here, we'll add an underlying variable if we have to
                  // ... but we should check that the mapping shape matches the archetype argument to which it applies
                  // otherwise we give malformed mappings / arguments a free pass, because the expr case does not
                  // actually guarantee any relationship between mapping and archetype argument, syntactically speaking
                  archetype.params(position) match {
                    case param @ MPCalRefParam(_, mappingCountP) =>
                      if (mappingCount != mappingCountP) {
                        errors += SemanticError.MPCalKindMismatchError(
                          usage = target,
                          defn = param,
                        )
                      }
                    case param @ MPCalValParam(_) =>
                      errors += SemanticError.MPCalMappingValueRefMismatchError(
                        usage = target,
                        defn = param,
                      )
                  }
              }
          }
          (archetype.params.view zip arguments.view).foreach {
            case (
                  MPCalRefParam(_, mappingCountP),
                  Left(MPCalRefExpr(_, mappingCount)),
                ) if mappingCount == mappingCountP => // ok
            case (
                  MPCalRefParam(_, _),
                  Right(_),
                ) => // ok, we'll add an underlying variable if we have to
            case (MPCalValParam(_), Right(_)) => // ok, pass by value
            case (param, Left(arg)) =>
              errors += SemanticError.MPCalKindMismatchError(
                usage = arg,
                defn = param,
              )
            // apparently unreachable, per Scala 3:
            // case (param, Right(arg)) =>
            //   errors += SemanticError.MPCalKindMismatchError(usage = arg, defn = param)
          }
      }

      def checkMPCalParamUsage(
          arguments: List[Either[MPCalRefExpr, TLAExpression]],
          params: List[MPCalParam],
      ): Unit =
        (arguments.view zip params.view).foreach {
          case (
                Left(MPCalRefExpr(_, mappingCount)),
                MPCalRefParam(_, mappingCountP),
              ) if mappingCount == mappingCountP => // ok
          case (Right(_: TLAExpression), MPCalValParam(_)) => // ok
          case (
                Right(_: TLAExpression),
                MPCalRefParam(_, _),
              ) => // special case: we should generate a synthetic local
          case (eitherArg, param) =>
            val arg: SourceLocatable = eitherArg match {
              case Left(value)  => value
              case Right(value) => value
            }
            errors += SemanticError.MPCalKindMismatchError(
              usage = arg,
              defn = param,
            )
        }

      block.visit(Visitable.TopDownFirstStrategy) {
        case instance @ MPCalInstance(_, _, _, arguments, _) =>
          if (instance.refersTo.params.size != arguments.size) {
            errors += SemanticError.PClArityMismatch(
              usage = instance,
              defn = instance.refersTo,
            )
          } else {
            checkMPCalParamUsage(arguments, instance.refersTo.params)
          }
        case PCalExtensionStatement(call @ MPCalCall(_, arguments)) =>
          if (call.refersTo.params.size != arguments.size) {
            errors += SemanticError.PClArityMismatch(
              usage = call,
              defn = call.refersTo,
            )
          } else {
            checkMPCalParamUsage(arguments, call.refersTo.params)
          }
      }
    }

    // check that mapping macros are not many-to-one
    // i.e that the same instance parameter is not mapped more than one way
    block.visit(Visitable.TopDownFirstStrategy) {
      case MPCalInstance(_, _, _, _, mappings) =>
        val visitedPositions = mutable.HashMap[Int, MPCalMapping]()
        mappings.foreach { case mapping @ MPCalMapping(target, _) =>
          if (!visitedPositions.contains(target.position)) {
            visitedPositions.update(target.position, mapping)
          } else {
            errors += SemanticError.MPCalMultipleMapping(
              visitedPositions(target.position),
              mapping,
            )
          }
        }
    }

    // check that assignments are only to assignable things, which are all state variables, or indirect references to them
    // these are, exhaustively:
    // - local or global state vars
    // - archetype and procedure params
    //
    // strategy: capture all these things, then look for assignments to things that are not them
    locally {
      // gather all the assignable things
      val assignableThings: Set[ById[DefinitionOne]] = {
        var assignableThingsAcc: Set[ById[DefinitionOne]] = Set.empty
        block.visit(Visitable.TopDownFirstStrategy) {
          case arch: MPCalArchetype =>
            assignableThingsAcc ++= (arch.params.iterator ++ arch.variables)
              .map(ById(_))
          case proc: MPCalProcedure =>
            assignableThingsAcc ++= (proc.params.iterator ++ proc.variables)
              .map(ById(_))
          case proc: PCalProcedure =>
            assignableThingsAcc ++= (proc.params.iterator ++ proc.variables)
              .map(ById(_))
          case proc: PCalProcess =>
            assignableThingsAcc ++= (Iterator.single(
              proc.selfDecl,
            ) ++ proc.variables).map(ById(_))
        }
        assignableThingsAcc ++= block.variables.iterator.map(ById(_))
        assignableThingsAcc
      }

      block.visit(Visitable.TopDownFirstStrategy) {
        case _: PCalMacro => // don't look at macro bodies
        case PCalAssignmentPair(lhs, _) =>
          @tailrec
          def findRef(
              lhs: PCalAssignmentLhs,
          ): Option[PCalAssignmentLhsIdentifier] =
            lhs match {
              case ref: PCalAssignmentLhsIdentifier    => Some(ref)
              case PCalAssignmentLhsProjection(lhs, _) => findRef(lhs)
              case PCalAssignmentLhsExtension(MPCalDollarVariable()) => None
              case PCalAssignmentLhsExtension(locatable: SourceLocatable) =>
                errors += PCalInvalidAssignment(locatable)
                None
              case _ => !!!
            }

          findRef(lhs).foreach { ref =>
            if (!assignableThings(ById(ref.refersTo))) {
              errors += PCalInvalidAssignment(ref)
            }
          }
      }
    }

    if (errors.nonEmpty) {
      throw SemanticError(errors.result())
    }
  }
}
