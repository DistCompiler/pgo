package pgo.trans

import pgo.model.{Definition, DefinitionOne, PGoError, RefersTo, Rewritable, Visitable}
import pgo.model.mpcal._
import pgo.model.pcal._
import pgo.model.tla._
import pgo.util.Unreachable.!!!
import pgo.util.{IdMap, NameCleaner}

import scala.annotation.tailrec
import scala.collection.mutable

object MPCalPCalCodegenPass {
  @throws[PGoError]
  def apply(mpcalBlock: MPCalBlock): PCalAlgorithm = {
    var block: MPCalBlock = mpcalBlock

    val nameCleaner = new NameCleaner
    block.visit(Visitable.BottomUpFirstStrategy) {
      case TLAIdentifier(id) => nameCleaner.addKnownName(id)
    }

    // Expand mpcal procedures and mapping macros
    // - in any case, rename any local bindings in the read body
    // - for write, force the write into whatever nested position. there will only be one per nested stmt, so no need to worry about side-effects
    // - for read, more care is needed: the value that was read should be bound via "with" where it logically appears, and
    //   further read macros should be expanded inside the with body. if a yield is in non-tail position, interaction between multiple applications
    //   of the same mapping (multiple reads of the same value per-expression) will be unsound, as statements logically "after" the read may appear
    //   in positions that do not respect logical control flow. Note also that reads are treated syntactically, with the same syntactic read being
    //   expanded exactly once outside the containing expression, in all cases.
    //   Function-mapped reads that depend on quantified variables, or LET-bound variables, will not be treated soundly.
    block = locally {
      val generatedPCalProcedures = mutable.ListBuffer[PCalProcedure]()
      val generatedPCalProcesses = mutable.ListBuffer[PCalProcess]()
      // mpcal procedure expansion signature:
      // - identity of the mpcal procedure being expanded
      // - for a ref param, the identity of the param referenced (or, the expression, if that's the case), and the identity of the mapping to be applied
      // - for a non-ref [_] param, the identity of the mapping to be applied (but not the identity of what is referenced, as it is taken by-value)
      val mpcalProcedureCache = mutable.HashMap[List[TLAExpression],PCalProcedure]()

      object MappedRead {
        @tailrec
        private def unapplyImpl(expr: TLAExpression, mappingCount: Int): Option[(Int,TLAGeneralIdentifier)] =
          expr match {
            case TLAFunctionCall(fn, _) =>
              unapplyImpl(fn, mappingCount + 1)
            case ident: TLAGeneralIdentifier => Some((mappingCount, ident))
            case _ => None
          }

        def unapply(expr: TLAExpression): Option[(Int,TLAGeneralIdentifier)] =
          unapplyImpl(expr, mappingCount = 0)
      }

      def updateStmt(stmt: PCalStatement)(implicit mappingsMap: IdMap[DefinitionOne,(Int,MPCalMappingMacro)], substitutions: IdMap[RefersTo.HasReferences,DefinitionOne]): List[PCalStatement] = {
        var stmtSink: List[PCalStatement] => List[PCalStatement] = identity

        def updateReads[E <: Rewritable](expr: E, skipMappings: Boolean = false): E =
          expr.rewrite(Rewritable.TopDownFirstStrategy) {
            case expr@MappedRead(mappingCount, ident) if !skipMappings && mappingsMap.get(ident.refersTo).exists(_._1 == mappingCount) =>
              val (_, mapping) = mappingsMap(ident.refersTo)
              val translatedExpr = updateReads(expr, skipMappings = true)
              def translateLhs(expr: TLAExpression): PCalAssignmentLhs =
                expr match {
                  case expr@TLAGeneralIdentifier(name, Nil) => PCalAssignmentLhsIdentifier(name).setRefersTo(expr.refersTo)
                  case TLAFunctionCall(fn, arguments) => PCalAssignmentLhsProjection(translateLhs(fn), arguments)
                }

              val translatedLhs = translateLhs(translatedExpr)

              val placeholder = PCalVariableDeclarationValue(TLAIdentifier("THIS_IS_A_BUG"), TLAString("THIS IS A BUG"))

              val oldStmtSink = stmtSink
              stmtSink = { innerStmts =>
                oldStmtSink {
                  mapping.readBody.mapConserve(_.rewrite(Rewritable.BottomUpOnceStrategy) {
                    case PCalAssignmentLhsExtension(MPCalDollarVariable()) => translatedLhs
                    case TLAExtensionExpression(MPCalDollarVariable()) => translatedExpr
                    case PCalExtensionStatement(MPCalYield(valExpr)) =>
                      val yieldedBind = PCalVariableDeclarationValue(TLAIdentifier(nameCleaner.cleanName("yielded")), valExpr)
                      PCalWith(List(yieldedBind),
                        innerStmts.mapConserve(_.rewrite(Rewritable.BottomUpOnceStrategy) {
                          case ident: TLAGeneralIdentifier if ident.refersTo eq placeholder =>
                            TLAGeneralIdentifier(yieldedBind.name, Nil).setRefersTo(yieldedBind)
                        })
                      )
                  })
                }
              }
              TLAGeneralIdentifier(placeholder.name, Nil).setRefersTo(placeholder)
            case ident@TLAGeneralIdentifier(_, prefix) if substitutions.contains(ident.refersTo) =>
              val mappedPrefix = prefix.mapConserve(updateReads(_))
              val subDefn = substitutions(ident.refersTo)
              val name = subDefn.identifier.asInstanceOf[Definition.ScopeIdentifierName].name
              TLAGeneralIdentifier(name, mappedPrefix).setRefersTo(subDefn)
          }

        val unwrappedStmt = stmt match {
          case stmt: PCalAssignment =>
            @tailrec
            def findRef(lhs: PCalAssignmentLhs): Option[PCalAssignmentLhsIdentifier] =
              lhs match {
                case ident: PCalAssignmentLhsIdentifier => Some(ident)
                case PCalAssignmentLhsProjection(lhs, _) => findRef(lhs)
              }

            def replaceRef(lhs: PCalAssignmentLhs): PCalAssignmentLhs =
              lhs match {
                case ident: PCalAssignmentLhsIdentifier if substitutions.contains(ident.refersTo) =>
                  val sub = substitutions(ident.refersTo)
                  PCalAssignmentLhsIdentifier(sub.identifier.asInstanceOf[Definition.ScopeIdentifierName].name)
                    .setRefersTo(sub)
                case ident: PCalAssignmentLhsIdentifier => ident
                case proj@PCalAssignmentLhsProjection(lhs, projections) =>
                  proj.withChildren(Iterator(replaceRef(lhs), projections))
              }

            def splitLhs(lhs: PCalAssignmentLhs, mappingCount: Int): (PCalAssignmentLhs, PCalAssignmentLhs=>PCalAssignmentLhs) = {
              assert(mappingCount >= 0)
              @tailrec
              def findDepth(lhs: PCalAssignmentLhs, acc: Int = 0): Int =
                lhs match {
                  case PCalAssignmentLhsIdentifier(_) => acc
                  case PCalAssignmentLhsProjection(lhs, _) => findDepth(lhs, acc + 1)
                }

              val depth = findDepth(lhs)
              @tailrec
              def findMappedLhs(lhs: PCalAssignmentLhs, layersToDiscard: Int): PCalAssignmentLhs = {
                assert(layersToDiscard >= 0)
                if(layersToDiscard == 0) {
                  replaceRef(lhs)
                } else {
                  val PCalAssignmentLhsProjection(innerLhs, _) = lhs
                  findMappedLhs(innerLhs, layersToDiscard - 1)
                }
              }
              // FIXME: the wrapper for when depth > mappingCount
              (findMappedLhs(lhs, depth - mappingCount), identity)
            }

            def convertLhs(lhs: PCalAssignmentLhs): TLAExpression =
              lhs match {
                case lhs@PCalAssignmentLhsIdentifier(identifier) =>
                  TLAGeneralIdentifier(identifier, Nil)
                    .setRefersTo(lhs.refersTo)
                case PCalAssignmentLhsProjection(lhs, projections) =>
                  TLAFunctionCall(convertLhs(lhs), projections)
              }

            val withReads@PCalAssignment(List(PCalAssignmentPair(lhs, rhs))) = updateReads(stmt)
            findRef(lhs).flatMap {
              case ident if mappingsMap.contains(ident.refersTo) =>
                val (mappingCount, mapping) = mappingsMap(ident.refersTo)
                val (mappedLhs, lhsReplacer) = splitLhs(lhs, mappingCount)
                val convertedLhs = convertLhs(mappedLhs)
                val valueBind = PCalVariableDeclarationValue(TLAIdentifier(nameCleaner.cleanName("value")), rhs)
                Some {
                  PCalWith(List(valueBind), mapping.writeBody.mapConserve(_.rewrite(Rewritable.BottomUpOnceStrategy) {
                    case PCalAssignmentLhsExtension(MPCalDollarVariable()) =>
                      mappedLhs
                    case TLAExtensionExpression(MPCalDollarValue()) =>
                      TLAGeneralIdentifier(valueBind.name, Nil).setRefersTo(valueBind)
                    case TLAExtensionExpression(MPCalDollarVariable()) =>
                      convertedLhs
                    case PCalExtensionStatement(MPCalYield(yieldedExpr)) =>
                      // FIXME: account for "extra" lhs parts
                      PCalAssignment(List(PCalAssignmentPair(mappedLhs, yieldedExpr)))
                  }))
                }
              case _ => None
            }.getOrElse(withReads)
          case stmt@PCalEither(cases) =>
            stmt.withChildren(Iterator(
              cases.map(_.flatMap(updateStmt))
            ))
          case stmt@PCalIf(condition, yes, no) =>
            stmt.withChildren(Iterator(
              updateReads(condition),
              yes.flatMap(updateStmt),
              no.flatMap(updateStmt),
            ))
          case stmt@PCalLabeledStatements(label, statements) =>
            stmt.withChildren(Iterator(label, statements.flatMap(updateStmt)))
          case PCalMacroCall(_, _) => !!!
          case PCalWhile(_, _) => !!!
          case stmt@PCalWith(variables, body) =>
            stmt.withChildren(Iterator(
              variables.mapConserve(updateReads(_)),
              body.flatMap(updateStmt),
            ))
          case PCalExtensionStatement(MPCalCall(target, arguments)) =>
            ??? // TODO: correctly handle refs, that is, ensure that the mpcal procedure is instantiated correctly,
          // and that substitutions are also applied correctly
          // (substitutions will remove refs/function mappings, by design, but also breaking procedure signatures)
          case stmt => updateReads(stmt)
        }
        stmtSink(List(unwrappedStmt))
      }

      // TODO: single-process MPCal
      val rewritten = block.rewrite(Rewritable.TopDownFirstStrategy) {
        case instance @MPCalInstance(selfDecl, fairness, archetypeName, arguments, mappings) =>
          val archetype = instance.refersTo

          val substitutionsBuilder = mutable.Buffer.empty[(RefersTo.HasReferences,DefinitionOne)]
          val variables = archetype.variables.iterator.map { v =>
            val clone = v.shallowCopy()
            substitutionsBuilder += v -> clone
            clone
          }.to(mutable.ListBuffer)
          (arguments.iterator zip archetype.params).foreach {
            case Left(arg @MPCalRefExpr(_, _)) -> param =>
              substitutionsBuilder += param -> arg.refersTo
            case Left(arg @MPCalValExpr(_, _)) -> param =>
              variables += PCalVariableDeclarationValue(param.name, TLAGeneralIdentifier(arg.name, Nil).setRefersTo(arg.refersTo))
              substitutionsBuilder += param -> variables.last
            case Right(expr) -> param =>
              variables += PCalVariableDeclarationValue(param.name, expr)
              substitutionsBuilder += param -> variables.last
          }
          val substitutions = IdMap.from(substitutionsBuilder)

          val mappingsMap = mappings.iterator.map {
            case mapping @MPCalMapping(MPCalMappingTarget(index, mappingCount), _) =>
              val param = archetype.params(index)
              (param: DefinitionOne) -> (mappingCount, mapping.refersTo)
          }.to(IdMap)

          generatedPCalProcesses += PCalProcess(
            selfDecl, fairness, variables.result(),
            archetype.body.flatMap(updateStmt(_)(substitutions = substitutions, mappingsMap = mappingsMap))
          ).setSourceLocation(instance.sourceLocation)

          instance // return the instance unchanged; we got what we came for
        case proc@PCalProcess(selfDecl, fairness, variables, body) =>
          proc.withChildren(Iterator(selfDecl, fairness, variables,
            body.flatMap(updateStmt(_)(substitutions = IdMap.empty, mappingsMap = IdMap.empty))))
        case proc@PCalProcedure(name, params, variables, body) =>
          proc.withChildren(Iterator(name, params, variables,
            body.flatMap(updateStmt(_)(substitutions = IdMap.empty, mappingsMap = IdMap.empty))))
      }

      rewritten.copy(
        pcalProcedures = generatedPCalProcedures.result(),
        mappingMacros = Nil,
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

    // desugar all non-trivial (e.g just to a name) assignments, using the TLA+ EXCEPT expression where appropriate
    // rationale: this makes it a lot easier to repair any "multiple write within same label" issues induced by MPCal expansion
    //            as plain assignments match with statement semantics, vs. just needing to do the same transformation in-line
    //            with repairs anyway, which is more complicated
    block = block.rewrite(Rewritable.BottomUpOnceStrategy) {
      case PCalAssignment(List(PCalAssignmentPair(lhs, rhs))) =>
        @tailrec
        def findIdent(lhs: PCalAssignmentLhs): PCalAssignmentLhsIdentifier =
          lhs match {
            case lhs: PCalAssignmentLhsIdentifier => lhs
            case PCalAssignmentLhsProjection(lhs, _) => findIdent(lhs)
          }

        @tailrec
        def findSubstitutionKeys(lhs: PCalAssignmentLhs, keysAcc: mutable.ListBuffer[TLAFunctionSubstitutionKey]): List[TLAFunctionSubstitutionKey] =
          lhs match {
            case PCalAssignmentLhsIdentifier(_) => keysAcc.result()
            case PCalAssignmentLhsProjection(lhs, projections) =>
              keysAcc += TLAFunctionSubstitutionKey(projections)
              findSubstitutionKeys(lhs, keysAcc)
          }

        val ident = findIdent(lhs)
        val substitutionKeys = findSubstitutionKeys(lhs, mutable.ListBuffer.empty)
        val wrappedRhs =
          if(substitutionKeys.isEmpty) {
            rhs
          } else {
            TLAFunctionSubstitution(
              source = TLAGeneralIdentifier(ident.identifier, Nil).setRefersTo(ident.refersTo),
              substitutions = List(TLAFunctionSubstitutionPair(
                anchor = TLAFunctionSubstitutionPairAnchor(),
                keys = substitutionKeys,
                value = rhs))
            )
          }

        PCalAssignment(List(PCalAssignmentPair(ident, wrappedRhs)))
    }

    // TODO: deduplicate repeat assignments within the same label, by lifting non-final assignments to with statements
    /*block = locally {


      block.rewrite(Rewritable.TopDownFirstStrategy) {
        case PCalLabeledStatements(label, body) =>
          ???
      }
    }*/

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
