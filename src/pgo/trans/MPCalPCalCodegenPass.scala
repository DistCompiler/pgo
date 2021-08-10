package pgo.trans

import pgo.model.Definition.ScopeIdentifierName
import pgo.model.{Definition, DefinitionOne, PGoError, RefersTo, Rewritable, SourceLocation, Visitable}
import pgo.model.mpcal._
import pgo.model.pcal._
import pgo.model.tla._
import pgo.util.Description._
import pgo.util.MPCalPassUtils.MappedRead
import pgo.util.Unreachable.!!!
import pgo.util.{Description, IdMap, NameCleaner}

import scala.annotation.tailrec
import scala.collection.mutable

object MPCalPCalCodegenPass {
  final class MPCalPCalEffectivelyNoProcessesError(mpcalBlock: MPCalBlock) extends PGoError {
    override val errors: List[PGoError.Error] =
      List(MPCalPCalEffectivelyNoProcessesError.MPCalEffectivelyNoProcesses(mpcalBlock))
  }
  object MPCalPCalEffectivelyNoProcessesError {
    final case class MPCalEffectivelyNoProcesses(mpcalBlock: MPCalBlock) extends PGoError.Error {
      override def sourceLocation: SourceLocation = mpcalBlock.sourceLocation
      override val description: Description = d"Modular PlusCal block has effectively no processes"
    }
  }

  @throws[PGoError]
  def apply(tlaModule: TLAModule, mpcalBlock: MPCalBlock): PCalAlgorithm = {
    var block: MPCalBlock = mpcalBlock

    // if the block effectively has no processes _at all_, we can't generate a valid PCal algorithm from it
    // we can generate Go code though, so this check shouldn't be a general semantic check; it's the only codegen check
    block.processes match {
      case Left(_) => // this check doesn't matter for single-process in any case (though it's unsupported below)
      case Right(processes) =>
        if(processes.isEmpty && block.instances.isEmpty) {
          throw new MPCalPCalEffectivelyNoProcessesError(block)
        }
    }

    val nameCleaner = new NameCleaner
    tlaModule.visit(Visitable.BottomUpFirstStrategy) {
      case TLAIdentifier(id) => nameCleaner.addKnownName(id)
    }
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
      // TODO mpcal procedure expansion signature:
      // - identity of the mpcal procedure being expanded
      // - for a ref param, the identity of the param referenced (or, the expression, if that's the case), and the identity of the mapping to be applied
      // - for a non-ref [_] param, the identity of the mapping to be applied (but not the identity of what is referenced, as it is taken by-value)
      val mpcalProcedureCache = mutable.HashMap[List[TLAExpression],PCalProcedure]()

      /**
       * Transform the statement according to the provided substitutions. Accounts for assignment LHS, but
       * will not work for unusual things like $variable and $value, or if the replacement does not have an
       * alphanumeric name (that can is represented as a TLAIdentifier).
       */
      def applySubstitutions(stmt: PCalStatement)(implicit substitutions: IdMap[RefersTo.HasReferences,DefinitionOne]): PCalStatement =
        stmt.rewrite(Rewritable.TopDownFirstStrategy ) {
          case ident@TLAGeneralIdentifier(_, pfx) if substitutions.contains(ident.refersTo) =>
            assert(pfx.isEmpty)
            val sub = substitutions(ident.refersTo)
            TLAGeneralIdentifier(sub.identifier.asInstanceOf[ScopeIdentifierName].name, pfx).setRefersTo(sub)
          case lhs@PCalAssignmentLhsIdentifier(_) if substitutions.contains(lhs.refersTo) =>
            val sub = substitutions(lhs.refersTo)
            PCalAssignmentLhsIdentifier(sub.identifier.asInstanceOf[ScopeIdentifierName].name).setRefersTo(sub)
        }

      /**
       * Transform the statement according to the provided mapping macros. Does not rename anything - that's done separately,
       * after the transformation.
       */
      def applyMappingMacros(stmt: PCalStatement)(implicit mappingsMap: IdMap[DefinitionOne,(Int,MPCalMappingMacro)], selfDecl: DefinitionOne): List[PCalStatement] = {
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
                  case _ => !!! // MappedRead matching should ensure exhaustivity of the cases above
                }

              val translatedLhs = translateLhs(translatedExpr)

              val placeholder = PCalVariableDeclarationValue(TLAIdentifier("THIS_IS_A_BUG"), TLAString("THIS IS A BUG"))

              val oldStmtSink = stmtSink
              stmtSink = { innerStmts =>
                oldStmtSink {
                  mapping.readBody.mapConserve(_.rewrite(Rewritable.BottomUpOnceStrategy) {
                    case ident: TLAGeneralIdentifier if ident.refersTo eq mapping.selfDecl =>
                      TLAGeneralIdentifier(TLAIdentifier("self"), Nil).setRefersTo(selfDecl)
                    case PCalAssignmentLhsExtension(MPCalDollarVariable()) => translatedLhs
                    case TLAExtensionExpression(MPCalDollarVariable()) => translatedExpr
                    case PCalExtensionStatement(MPCalYield(valExpr)) =>
                      val yieldedBind = PCalVariableDeclarationValue(TLAIdentifier(nameCleaner.cleanName(s"yielded_${ident.name.id}")), valExpr)
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
          }

        val unwrappedStmt = stmt match {
          case stmt: PCalAssignment =>
            @tailrec
            def findRef(lhs: PCalAssignmentLhs): Option[PCalAssignmentLhsIdentifier] =
              lhs match {
                case ident: PCalAssignmentLhsIdentifier => Some(ident)
                case PCalAssignmentLhsProjection(lhs, _) => findRef(lhs)
                case PCalAssignmentLhsExtension(_) => !!! // shouldn't happen
              }

            @tailrec
            def findLhsDepth(lhs: PCalAssignmentLhs, acc: Int = 0): Int =
              lhs match {
                case PCalAssignmentLhsIdentifier(_) => acc
                case PCalAssignmentLhsProjection(lhs, _) => findLhsDepth(lhs, acc + 1)
                case PCalAssignmentLhsExtension(_) => !!! // shouldn't happen
              }

            def convertLhs(lhs: PCalAssignmentLhs): TLAExpression =
              lhs match {
                case lhs@PCalAssignmentLhsIdentifier(identifier) =>
                  TLAGeneralIdentifier(identifier, Nil)
                    .setRefersTo(lhs.refersTo)
                case PCalAssignmentLhsProjection(lhs, projections) =>
                  TLAFunctionCall(convertLhs(lhs), projections)
                case PCalAssignmentLhsExtension(_) => !!! // shouldn't happen
              }

            val withReads@PCalAssignment(List(PCalAssignmentPair(lhs, rhs))) = updateReads(stmt)
            findRef(lhs).flatMap {
              case ident if mappingsMap.contains(ident.refersTo) =>
                val (mappingCount, mapping) = mappingsMap(ident.refersTo)
                // TODO: maybe implement depth > mappingCount, but it may be more confusion than it's worth
                // for now, assert that it's not the case, to avoid very confusion mis-compilations
                assert(mappingCount == findLhsDepth(lhs))
                val convertedLhs = convertLhs(lhs)
                val valueBind = PCalVariableDeclarationValue(TLAIdentifier(nameCleaner.cleanName("value")), rhs)
                Some {
                  PCalWith(List(valueBind), mapping.writeBody.mapConserve(_.rewrite(Rewritable.BottomUpOnceStrategy) {
                    case ident: TLAGeneralIdentifier if ident.refersTo eq mapping.selfDecl =>
                      TLAGeneralIdentifier(TLAIdentifier("self"), Nil).setRefersTo(selfDecl)
                    case PCalAssignmentLhsExtension(MPCalDollarVariable()) =>
                      lhs
                    case TLAExtensionExpression(MPCalDollarValue()) =>
                      TLAGeneralIdentifier(valueBind.name, Nil).setRefersTo(valueBind)
                    case TLAExtensionExpression(MPCalDollarVariable()) =>
                      convertedLhs
                    case PCalExtensionStatement(MPCalYield(yieldedExpr)) =>
                      PCalAssignment(List(PCalAssignmentPair(lhs, yieldedExpr)))
                  }))
                }
              case _ => None
            }.getOrElse(withReads)
          case stmt@PCalEither(cases) =>
            stmt.withChildren(Iterator(
              cases.map(_.flatMap(applyMappingMacros))
            ))
          case stmt@PCalIf(condition, yes, no) =>
            stmt.withChildren(Iterator(
              updateReads(condition),
              yes.flatMap(applyMappingMacros),
              no.flatMap(applyMappingMacros),
            ))
          case stmt@PCalLabeledStatements(label, statements) =>
            stmt.withChildren(Iterator(label, statements.flatMap(applyMappingMacros)))
          case PCalMacroCall(_, _) => !!!
          case PCalWhile(_, _) => !!!
          case stmt@PCalWith(variables, body) =>
            stmt.withChildren(Iterator(
              variables.mapConserve(updateReads(_)),
              body.flatMap(applyMappingMacros),
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
            archetype.body.view
              .flatMap(applyMappingMacros(_)(mappingsMap = mappingsMap, selfDecl = selfDecl))
              .map(applySubstitutions(_)(substitutions = substitutions)) // subs after mapping macros, to deal with many-to-one subs
              .toList
          ).setSourceLocation(instance.sourceLocation)

          instance // return the instance unchanged; we got what we came for
        case proc@PCalProcess(selfDecl, fairness, variables, body) =>
          proc.withChildren(Iterator(selfDecl, fairness, variables,
            body.flatMap(applyMappingMacros(_)(mappingsMap = IdMap.empty, selfDecl = selfDecl))))
        case proc@PCalProcedure(name, selfDecl, params, variables, body) =>
          proc.withChildren(Iterator(name, params, variables,
            body.flatMap(applyMappingMacros(_)(mappingsMap = IdMap.empty, selfDecl = selfDecl))))
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

    // desugar all non-trivial (e.g not just to a name) assignments, using the TLA+ EXCEPT expression where appropriate
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
            case PCalAssignmentLhsExtension(_) => !!! // shouldn't happen
          }

        @tailrec
        def findSubstitutionKeys(lhs: PCalAssignmentLhs, keysAcc: mutable.ListBuffer[TLAFunctionSubstitutionKey]): List[TLAFunctionSubstitutionKey] =
          lhs match {
            case PCalAssignmentLhsIdentifier(_) => keysAcc.result()
            case PCalAssignmentLhsProjection(lhs, projections) =>
              keysAcc += TLAFunctionSubstitutionKey(projections)
              findSubstitutionKeys(lhs, keysAcc)
            case PCalAssignmentLhsExtension(_) => !!! // shouldn't happen
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

    // deduplicate repeat assignments within the same label, by lifting non-final assignments to with statements
    // rough strategy:
    //  1. count assignments to each variable within a given block (group of labeled statements), over-approximating branches
    //  2. have a memoized (maybe efficient) way to query the assignment counters over a given list of stmts
    //  3. while folding statements after any branching statement into each branch (causing AST duplication, yes)...
    //  3a. for any assignment to a variable whose count in the remaining statements (aka. the rest of that control flow path)
    //      is >= 1, lift that statement into a with-binding. record which assigned variables are "lifted" like this
    //  3b. for any assignment to a variable whose count in the remaining statements is 0 (aka. is the last one, or the only)
    //      ensure that records of any with-bindings are removed. this variable is "normally assigned" again.
    //  4. when the end of a path is reached, generate synthetic assignments from any remaining "lifted" vars to the actual variable
    block = locally {
      implicit class CountOps(val self: IdMap[DefinitionOne,Int]) {
        def +++(other: IdMap[DefinitionOne,Int]): IdMap[DefinitionOne,Int] =
          (self.keysIterator ++ other.keysIterator).map { defn =>
            defn -> (self.getOrElse(defn, 0) + other.getOrElse(defn, 0))
          }.to(IdMap)

        def |||(other: IdMap[DefinitionOne,Int]): IdMap[DefinitionOne,Int] =
          (self.keysIterator ++ other.keysIterator).map { defn =>
            defn -> (self.getOrElse(defn, 0) max other.getOrElse(defn, 0))
          }.to(IdMap)
      }

      block.rewrite(Rewritable.TopDownFirstStrategy) {
        case labeledStmts@PCalLabeledStatements(label, body) =>
          var assignmentCountsStmt = IdMap.empty[PCalStatement,IdMap[DefinitionOne,Int]]

          def calculateAssignmentCounts(body: List[PCalStatement]): IdMap[DefinitionOne,Int] = {
            var result = IdMap.empty[DefinitionOne,Int]
            body.foreach(_.visit(Visitable.TopDownFirstStrategy) {
              case stmt: PCalStatement if assignmentCountsStmt.contains(stmt) =>
                result +++= assignmentCountsStmt(stmt)
              case PCalIf(_, yes, no) =>
                result +++= (calculateAssignmentCounts(yes) ||| calculateAssignmentCounts(no))
              case PCalEither(cases) =>
                result +++= cases.iterator.map(calculateAssignmentCounts).reduce(_ ||| _)
              case PCalAssignment(List(PCalAssignmentPair(lhs: PCalAssignmentLhsIdentifier, _))) =>
                result = result.updated(lhs.refersTo, result.getOrElse(lhs.refersTo, 0) + 1)
            })
            result
          }

          body.foreach(_.visit(Visitable.BottomUpFirstStrategy) {
            case stmt: PCalStatement =>
              val counts = calculateAssignmentCounts(List(stmt))
              assignmentCountsStmt = assignmentCountsStmt.updated(stmt, counts)
          })

          var assignmentCountsMap = IdMap.empty[List[PCalStatement],IdMap[DefinitionOne,Int]]
          def assignmentCounts(stmts: List[PCalStatement]): IdMap[DefinitionOne,Int] =
            assignmentCountsMap.getOrElse(stmts, {
              val result = stmts match {
                case Nil => IdMap.empty[DefinitionOne,Int]
                case hd :: tl => assignmentCountsStmt(hd) +++ assignmentCounts(tl)
              }
              assignmentCountsMap = assignmentCountsMap.updated(stmts, result)
              result
            })

          object TailJumpStmts {
            // match all cases where a block of PCal ends in a jump
            def unapply(stmts: List[PCalStatement]): Option[List[PCalStatement]] =
              stmts match {
                case PCalGoto(_) :: Nil => Some(stmts)
                case PCalCall(_, _) :: (((PCalReturn() | PCalGoto(_)) :: Nil) | Nil) => Some(stmts)
                case PCalExtensionStatement(MPCalCall(_, _)) :: (((PCalReturn() | PCalGoto(_)) :: Nil) | Nil) => Some(stmts)
                case Nil => Some(Nil)
                case _ => None
              }
          }

          def impl(stmts: List[PCalStatement], substitutions: IdMap[DefinitionOne,DefinitionOne], lifted: List[(DefinitionOne,DefinitionOne)]): List[PCalStatement] = {
            /**
             * Perform substitutions, _specifically avoiding assignment LHS_! Fundamentally, these subs are for
             * temporary with-bindings, and they should never change an assignment target.
             *
             * "Adding the LHS case in the hope it would fix something, only to break something" count of shame: 1, pre-comment
             */
            def performSubstitutions(stmt: PCalStatement): PCalStatement =
              stmt.rewrite(Rewritable.BottomUpOnceStrategy) {
                case ident@TLAGeneralIdentifier(_, pfx) if substitutions.contains(ident.refersTo) =>
                  val sub = substitutions(ident.refersTo)
                  ident.withChildren(Iterator(sub.identifier.asInstanceOf[Definition.ScopeIdentifierName].name, pfx)).setRefersTo(sub)
              }

            @tailrec
            def endsInJump(stmts: List[PCalStatement]): Boolean =
              stmts match {
                case TailJumpStmts(stmts) if stmts.nonEmpty => true
                case _ :: tl => endsInJump(tl)
                case Nil => false
              }

            // concatenates two blocks, but only if the "first" block won't jump away, making the second unreachable
            // if that would be the case, it just returns the first block
            def jumpAwareConcat(beforeStmts: List[PCalStatement], afterStmts: List[PCalStatement]): List[PCalStatement] =
              if(endsInJump(beforeStmts)) {
                beforeStmts
              } else {
                beforeStmts ::: afterStmts
              }

            stmts match {
              case TailJumpStmts(tailStmts) =>
                // make "official" any prior writes bound to "with" stmts which were not written out already
                lifted.map {
                  case liftedFrom -> liftedTo =>
                    PCalAssignment(List(PCalAssignmentPair(
                      PCalAssignmentLhsIdentifier(liftedFrom.identifier.asInstanceOf[Definition.ScopeIdentifierName].name).setRefersTo(liftedFrom),
                      TLAGeneralIdentifier(liftedTo.identifier.asInstanceOf[Definition.ScopeIdentifierName].name, Nil).setRefersTo(liftedTo),
                    )))
                } ::: tailStmts.mapConserve(performSubstitutions) // make sure call args get replaced, because they might use with-bound names that have changed
              case Nil => !!! // taken care of by TailJumpStmts, but scalac doesn't know that
              case hd :: tl =>
                val hdRewritten = performSubstitutions(hd)
                hdRewritten match {
                  case PCalAssignment(List(PCalAssignmentPair(lhs: PCalAssignmentLhsIdentifier, rhs))) if assignmentCounts(tl).getOrElse(lhs.refersTo, 0) >= 1 =>
                    val rebind = PCalVariableDeclarationValue(TLAIdentifier(nameCleaner.cleanName(lhs.identifier.id)), rhs)
                    List(PCalWith(List(rebind),
                      impl(tl, substitutions.updated(lhs.refersTo, rebind), (lhs.refersTo, rebind) :: lifted)
                    ))
                  case stmt @PCalAssignment(List(PCalAssignmentPair(lhs: PCalAssignmentLhsIdentifier, _))) if assignmentCounts(tl).getOrElse(lhs.refersTo, 0) == 0 =>
                    // if this was the last assignment, leave it intact, and remove data that would have a second "last assignment" generated at end of block
                    stmt :: impl(tl, substitutions - lhs.refersTo, lifted.filter(_._1 ne lhs.refersTo))
                  case PCalWith(bindings, body) if tl.isEmpty =>
                    List(PCalWith(bindings, impl(body, substitutions, lifted)))
                  case PCalWith(bindings, body) =>
                    // push the remaining statements inside the body, so lifted assignments are guaranteed to be in scope
                    // for the entire critical section. to avoid name collisions, conservatively rename all bindings to fresh names
                    val renamedBindings = bindings.map {
                      case PCalVariableDeclarationValue(name, value) =>
                        PCalVariableDeclarationValue(TLAIdentifier(nameCleaner.cleanName(name.id)), value)
                      case PCalVariableDeclarationSet(name, set) =>
                        PCalVariableDeclarationSet(TLAIdentifier(nameCleaner.cleanName(name.id)), set)
                    }
                    List(PCalWith(renamedBindings,
                      impl(body ::: tl, substitutions ++ (bindings.iterator zip renamedBindings), lifted)))
                  case PCalIf(cond, yes, no) =>
                    List(PCalIf(
                      cond,
                      impl(jumpAwareConcat(yes, tl), substitutions, lifted),
                      impl(jumpAwareConcat(no, tl), substitutions, lifted)))
                  case PCalEither(cases) =>
                    List(PCalEither(cases.map(cse => impl(jumpAwareConcat(cse, tl), substitutions, lifted))))
                  case stmt =>
                    stmt :: impl(tl, substitutions, lifted)
                }
            }
          }

          labeledStmts.withChildren(Iterator(label, impl(body, IdMap.empty, Nil)))
      }
    }

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
