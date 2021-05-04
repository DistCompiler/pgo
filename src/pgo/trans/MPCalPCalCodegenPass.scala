package pgo.trans

import pgo.model.{Definition, DefinitionOne, PGoError, RefersTo, Rewritable, SourceLocation}
import pgo.model.mpcal._
import pgo.model.pcal._
import pgo.model.tla._
import pgo.util.{IdMap, IdSet}

import scala.annotation.tailrec
import scala.collection.{immutable, mutable}

object MPCalPCalCodegenPass {
  @throws[PGoError]
  def apply(mpcalBlock: MPCalBlock): PCalAlgorithm = {
    var block: MPCalBlock = mpcalBlock

    block = locally {
      val generatedPCalProcedures = mutable.ListBuffer[PCalProcedure]()
      val generatedPCalProcesses = mutable.ListBuffer[PCalProcess]()
      // mpcal procedure expansion signature:
      // - identity of the mpcal procedure being expanded
      // - for a ref param, the identity of the param referenced (or, the expression, if that's the case), and the identity of the mapping to be applied
      // - for a non-ref [_] param, the identity of the mapping to be applied (but not the identity of what is referenced, as it is taken by-value)
      val mpcalProcedureCache = mutable.HashMap[List[TLAExpression],PCalProcedure]()

      def impl(stmts: List[PCalStatement], inProcedures: IdSet[MPCalProcedure]): List[PCalStatement] = {
        stmts.flatMap {
          case PCalAssignment(List(PCalAssignmentPair(lhs, rhs))) =>
            ???
          case PCalAssignment(moreThanOnePair) => ??? // should be unreachable
          case PCalExtensionStatement(MPCalCall(target, arguments)) =>
            ???
        }
      }

      // TODO: single-process MPCal
      val rewritten = block.rewrite(Rewritable.TopDownFirstStrategy) {
        case instance @MPCalInstance(selfDecl, fairness, archetypeName, arguments, mappings) =>
          val archetype = instance.refersTo

          val substitutionsBuilder = immutable.Map.newBuilder[RefersTo.HasReferences,DefinitionOne]
          val variables = archetype.variables.iterator.map { v =>
            val clone = v.shallowCopy()
            substitutionsBuilder += v -> clone
            clone
          }.to(mutable.ListBuffer)
          (arguments.iterator zip archetype.params).foreach {
            case Left(arg @MPCalRefExpr(_, _)) -> param =>
              substitutionsBuilder += param -> arg.refersTo
            case Left(arg @MPCalValExpr(_, _)) -> param =>
              variables += PCalVariableDeclarationValue(param.name, TLAGeneralIdentifier(arg.name, Nil))
              substitutionsBuilder += param -> variables.last
            case Right(expr) -> param =>
              variables += PCalVariableDeclarationValue(param.name, expr)
              substitutionsBuilder += param -> variables.last
          }
          val substitutions = substitutionsBuilder.result()

          val mappingsMap = mappings.iterator.map {
            case mapping @MPCalMapping(MPCalMappingTarget(index, mappingCount), _) =>
              val param = archetype.params(index)
              (param: DefinitionOne) -> (mappingCount, mapping.refersTo)
          }.toMap

          def updateStmt(stmt: PCalStatement): PCalStatement = {
            // TODO: how to "interpolate" the mapping macro stmts into a read/write
            // - in any case, rename any local bindings in the read body
            // - for write, force the write into whatever nested position. there will only be one per nested stmt, so no need to worry about side-effects
            // - for read, more care is needed: the value that was read should be bound via "with" where it logically appears, and
            //   further read macros should be expanded inside the with body. if a yield is in non-tail position, interaction between multiple applications
            //   of the same mapping (multiple reads of the same value per-expression) will be unsound, as statements logically "after" the read may appear
            //   in positions that do not respect logical control flow. Note also that reads are treated syntactically, with the same syntactic read being
            //   expanded exactly once outside the containing expression, in all cases.
            //   Function-mapped reads that depend on quantified variables, or LET-bound variables, will not be treated soundly.
            import scala.util.control.TailCalls._

            var stmtSink: TailRec[PCalStatement] => PCalStatement = _.result

            object MappedRead {
              @tailrec
              private def unapplyImpl(rewritable: Rewritable, mappingCount: Int): Option[(Int,TLAGeneralIdentifier)] =
                rewritable match {
                  case TLAFunctionCall(fn, _) =>
                    unapplyImpl(fn, mappingCount + 1)
                  case ident: TLAGeneralIdentifier => Some((mappingCount, ident))
                  case _ => None
                }

              def unapply(rewritable: Rewritable): Option[(Int,TLAGeneralIdentifier)] =
                unapplyImpl(rewritable, mappingCount = 0)
            }

            def updateReads[T <: Rewritable](t: T): T = {
              var result: T = t
              result = t.rewrite(Rewritable.TopDownFirstStrategy) {
                case expr@ MappedRead(mappingCount, ident) =>
                  mappingsMap.get(ident.refersTo) match {
                    case Some((expectedMappingCount, mapping)) if expectedMappingCount == mappingCount =>
                      val mappedBind = PCalVariableDeclarationValue(???, expr.asInstanceOf[TLAExpression])

                      stmtSink = { innerStmt =>
                        stmtSink(innerStmt.flatMap { innerStmt =>
                          done(PCalWith(List(mappedBind),
                            mapping.readBody.mapConserve { stmt =>
                              stmt.rewrite(Rewritable.TopDownFirstStrategy) {
                                case PCalExtensionStatement(MPCalYield(expr)) =>
                                  val yieldedBind = PCalVariableDeclarationValue(???, expr)
                                  PCalWith(List(yieldedBind), List(innerStmt))
                              }
                            }
                          ))
                        })
                      }

                      ??? //TLAGeneralIdentifier(???, Nil).setRefersTo(yieldedBind)
                    case _ => expr
                  }
              }

              result = t.rewrite(Rewritable.BottomUpOnceStrategy) {
                case ident: TLAGeneralIdentifier if substitutions.contains(ident.refersTo) =>
                  val replacement = substitutions(ident.refersTo)
                  ident.shallowCopy().copy(name = replacement.identifier.asInstanceOf[Definition.ScopeIdentifierName].name).setRefersTo(replacement)
              }
              result
            }

            stmtSink(done {
              stmt match {
                case stmt: PCalAssignment =>
                  @tailrec
                  def getRef(lhs: PCalAssignmentLhs): Option[DefinitionOne] =
                    lhs match {
                      case ident: PCalAssignmentLhsIdentifier => Some(ident.refersTo)
                      case PCalAssignmentLhsProjection(lhs, _) => getRef(lhs)
                      case PCalAssignmentLhsExtension(_) => None
                    }

                  /*@tailrec
                  def findReceiver(lhs: PCalAssignmentLhs, mappingCount: Int): (PCalAssignmentLhs, ) = {
                    assert(mappingCount >= 0)
                    if (mappingCount == 0) lhs else {
                      lhs match {
                        case PCalAssignmentLhsIdentifier(identifier) => ???
                        case PCalAssignmentLhsProjection(lhs, projections) =>
                          findReceiver(lhs, mappingCount - 1)
                        case PCalAssignmentLhsExtension(contents) => ???
                      }
                    }
                  }*/

                  val withReads@PCalAssignment(List(PCalAssignmentPair(lhs, rhs))) = updateReads(stmt)
                  getRef(lhs).flatMap { ref =>
                    mappingsMap.get(ref).map {
                      case (mappingCount, MPCalMappingMacro(name, readBody, writeBody, freeVars)) =>
                        //val receiver = findReceiver(lhs, mappingCount)

                        ???
                    }
                  }.getOrElse(withReads)
                case stmt@PCalEither(cases) =>
                  stmt.withChildren(Iterator(
                    cases.mapConserve(_.mapConserve(updateStmt))
                  ))
                case stmt@PCalIf(condition, yes, no) =>
                  stmt.withChildren(Iterator(
                    updateReads(condition),
                    yes.mapConserve(updateStmt),
                    no.mapConserve(updateStmt),
                  ))
                case stmt@PCalLabeledStatements(label, statements) =>
                  stmt.withChildren(Iterator(label, statements.mapConserve(updateStmt)))
                case PCalMacroCall(_, _) => ???
                case PCalWhile(_, _) => ???
                case stmt@PCalWith(variables, body) =>
                  stmt.withChildren(Iterator(
                    variables.mapConserve(updateReads),
                    body.mapConserve(updateStmt),
                  ))
                case PCalExtensionStatement(MPCalCall(target, arguments)) =>
                  ??? // TODO: correctly handle refs, that is, ensure that the mpcal procedure is instantiated correctly,
                // and that substitutions are also applied correctly
                // (substitutions will remove refs/function mappings, by design, but also breaking procedure signatures)
                case stmt =>
                  updateReads(stmt)
              }
            })
          }

          generatedPCalProcesses += PCalProcess(selfDecl, fairness, variables.result(), ???)
            .setSourceLocation(instance.sourceLocation)

          instance // return the instance unchanged; we got what we came for
        case PCalProcess(selfDecl, fairness, variables, body) =>
          ???
        case PCalProcedure(name, params, variables, body) =>
          ???
      }

      rewritten.copy(
        pcalProcedures = generatedPCalProcedures.result(),
        mpcalProcedures = Nil,
        instances = Nil,
        processes = rewritten.processes match {
          case left @Left(_) =>
            assert(generatedPCalProcesses.isEmpty)
            left
          case Right(existingProcs) =>
            Right(existingProcs ::: generatedPCalProcesses.result())
        })
    }
    // expand archetypes + mapping macros (using list buffer accumulator for add'l stmts) + mpcal procedures
    // ensure single assignment to each var

    PCalAlgorithm(
      name = block.name,
      fairness = PCalFairness.Unfair,
      units = block.units,
      macros = Nil,
      variables = block.variables,
      procedures = block.pcalProcedures,
      processes = block.processes,
    ).setSourceLocation(block.sourceLocation)
  }
}
