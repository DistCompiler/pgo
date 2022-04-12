package pgo.trans

import pgo.model.Definition.ScopeIdentifierName
import pgo.model.{Definition, DefinitionOne, PGoError, RefersTo, Rewritable, SourceLocation, Visitable}
import pgo.model.mpcal._
import pgo.model.pcal._
import pgo.model.tla._
import pgo.util.Description._
import pgo.util.MPCalPassUtils.MappedRead
import pgo.util.{!!!, ById, Description, NameCleaner}

import scala.annotation.tailrec
import scala.collection.{View, mutable}

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

  final case class MPCalProcedureSignature(proc: ById[MPCalProcedure], refArgs: List[(ById[DefinitionOne],Option[ById[MPCalMappingMacro]])])

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

      // cache to properly resolve shared MPCal procedure expansions + recursion loops
      val mpcalProcedureCache = mutable.HashMap[MPCalProcedureSignature,Either[(TLAIdentifier, mutable.ListBuffer[PCalProcedure=>Unit]),PCalProcedure]]()

      // name cleaner specifically for state variables; avoid renaming state vars unnecessarily
      val stateVarNameCleaner = new NameCleaner
      block.variables.foreach { decl =>
        stateVarNameCleaner.addKnownName(decl.name.id)
      }
      block.pcalProcedures.foreach { proc =>
        proc.params.foreach(p => stateVarNameCleaner.addKnownName(p.name.id))
        proc.variables.foreach(p => stateVarNameCleaner.addKnownName(p.name.id))
      }
      block.processes match {
        case Left(_) =>
        case Right(processes) =>
          processes.foreach { proc =>
            proc.variables.foreach(p => stateVarNameCleaner.addKnownName(p.name.id))
          }
      }

      /**
       * Transform the statement according to the provided substitutions. Accounts for assignment LHS, but
       * will not work for unusual things like $variable and $value, or if the replacement does not have an
       * alphanumeric name (that can is represented as a TLAIdentifier).
       */
      def applySubstitutions[Node <: Rewritable](stmt: Node)(implicit substitutions: Map[ById[RefersTo.HasReferences],DefinitionOne]): Node = {
        if(substitutions.isEmpty) {
          stmt // we might be given a vacuous substitution set; if so, don't bother running rewrite
        } else {
          stmt.rewrite(Rewritable.TopDownFirstStrategy) {
            case ident@TLAGeneralIdentifier(_, pfx) if substitutions.contains(ById(ident.refersTo)) =>
              assert(pfx.isEmpty)
              val sub = substitutions(ById(ident.refersTo))
              TLAGeneralIdentifier(sub.identifier.asInstanceOf[ScopeIdentifierName].name, pfx).setRefersTo(sub)
            case lhs@PCalAssignmentLhsIdentifier(_) if substitutions.contains(ById(lhs.refersTo)) =>
              val sub = substitutions(ById(lhs.refersTo))
              PCalAssignmentLhsIdentifier(sub.identifier.asInstanceOf[ScopeIdentifierName].name).setRefersTo(sub)
            case ref@MPCalRefExpr(_, mappingCount) if substitutions.contains(ById(ref.refersTo)) =>
              val sub = substitutions(ById(ref.refersTo))
              MPCalRefExpr(sub.identifier.asInstanceOf[ScopeIdentifierName].name, mappingCount).setRefersTo(sub)
          }
        }
      }

      /**
       * Transforms any with-bindings in the provided PCal statement, such that the bound names use fresh names.
       * This is important when expanding mapping macros that contain with-bindings, because expanding the same
       * mapping macro twice might lead to one with-statement in the macro containing itself, leading to a scoping error.
       */
      def cleanWithBindings(stmt: PCalStatement): PCalStatement =
        stmt.rewrite(Rewritable.BottomUpOnceStrategy) {
          case wth@PCalWith(defns, body) =>
            val cleanedDefns = defns.map {
              case PCalVariableDeclarationValue(name, value) =>
                PCalVariableDeclarationValue(TLAIdentifier(nameCleaner.cleanName(name.id)), value)
              case PCalVariableDeclarationSet(name, set) =>
                PCalVariableDeclarationSet(TLAIdentifier(nameCleaner.cleanName(name.id)), set)
            }

            applySubstitutions(
              wth.withChildren(Iterator(cleanedDefns,body)))((defns.view.map(ById(_)) zip cleanedDefns).toMap)
        }

      /**
       * Transform the statement according to the provided mapping macros. Does not rename anything - that's done separately,
       * after the transformation.
       */
      def applyMappingMacros(stmt: PCalStatement)(implicit mappingsMap: Map[ById[DefinitionOne],(Int,MPCalMappingMacro)], selfDecl: DefinitionOne): List[PCalStatement] = {
        var stmtSink: List[PCalStatement] => List[PCalStatement] = identity

        def updateReads[E <: Rewritable](expr: E, skipMappings: Boolean = false): E =
          expr.rewrite(Rewritable.TopDownFirstStrategy) {
            case expr@MappedRead(mappingCount, ident) if !skipMappings && mappingsMap.get(ById(ident.refersTo)).exists(_._1 == mappingCount) =>
              val (_, mapping) = mappingsMap(ById(ident.refersTo))
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
                  mapping.readBody
                    .mapConserve(cleanWithBindings) // ensure contained with-bindings use fresh names
                    .mapConserve(_.rewrite(Rewritable.BottomUpOnceStrategy) {
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
              case ident if mappingsMap.contains(ById(ident.refersTo)) =>
                val (mappingCount, mapping) = mappingsMap(ById(ident.refersTo))
                // this should always be the case; it would be too confusing otherwise, as documented in
                // test/files/general/pcalgen/MappingMacroRWExpansion.tla
                assert(mappingCount == findLhsDepth(lhs))
                val convertedLhs = convertLhs(lhs)
                val valueBind = PCalVariableDeclarationValue(TLAIdentifier(nameCleaner.cleanName("value")), rhs)
                Some {
                  PCalWith(
                    List(valueBind),
                    mapping.writeBody
                      .mapConserve(cleanWithBindings) // ensure contained with-bindings use fresh names
                      .mapConserve(_.rewrite(Rewritable.BottomUpOnceStrategy) {
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
          case PCalWith(variables, body) =>
            // explicitly handle each binding in variables individually, so that any resource operations in
            // the variable decls occurs with the correct sequencing (and relative scoping, able to reference previous decls)
            variables match {
              case Nil => !!!
              case decl :: restDecls =>
                val subbedDecl = updateReads(decl)
                val localSubstitutions: Map[ById[RefersTo.HasReferences],DefinitionOne] =
                  if(subbedDecl ne decl) Map(ById(decl) -> subbedDecl) else Map.empty

                restDecls match {
                  case Nil =>
                    PCalWith(List(subbedDecl),
                      body.view
                        // because we manually passed over the declarations, renaming is not free here! we have to do it explicitly.
                        .map(applySubstitutions(_)(localSubstitutions))
                        .flatMap(applyMappingMacros)
                        .toList)
                  case restDecls =>
                    PCalWith(List(subbedDecl),
                      applyMappingMacros(
                        // see above about non-free renaming
                        applySubstitutions(PCalWith(restDecls, body))(localSubstitutions)))
                }
            }
          case PCalExtensionStatement(call@MPCalCall(_, arguments)) =>
            val mpcalProcedure = call.refersTo
            val byRefArgs = arguments.collect {
              case Left(ref) => ref
            }
            val byValueArgs = arguments.collect {
              case Right(expr) => updateReads(expr)
            }
            val refSignature = MPCalProcedureSignature(
              proc = ById(mpcalProcedure),
              refArgs = byRefArgs.map { ref =>
                ById(ref.refersTo) -> mappingsMap.get(ById(ref.refersTo)).map(_._2).map(ById(_))
              })

            val cacheRecord = mpcalProcedureCache.getOrElseUpdate(refSignature, Right {
              val freshName = TLAIdentifier(nameCleaner.cleanName(mpcalProcedure.name.id))

              // break potential recursions by inserting a "fix list" into the procedure cache
              // the recursive expansion will instead insert a deferred resolution into the list, that
              // we will call on the way back up
              val recursionFixList = mutable.ListBuffer[PCalProcedure=>Unit]()
              mpcalProcedureCache(refSignature) = Left((freshName, recursionFixList))

              val refParams = mpcalProcedure.params.collect { case ref: MPCalRefParam => ref }
              assert(refParams.size == byRefArgs.size)
              val valParams = mpcalProcedure.params.collect { case v: MPCalValParam => v }

              // clean things that match state vars, so we don't cause name conflicts during expansion
              val transformedValParams = valParams.map { p =>
                PCalPVariableDeclaration(TLAIdentifier(stateVarNameCleaner.cleanName(p.name.id)), None)
              }
              val transformedVariables = mpcalProcedure.variables.map {
                case PCalPVariableDeclaration(name, value) =>
                  PCalPVariableDeclaration(TLAIdentifier(stateVarNameCleaner.cleanName(name.id)), value)
              }
              val freshSelfDecl = mpcalProcedure.selfDecl.shallowCopy()

              val substitutions: Map[ById[RefersTo.HasReferences],DefinitionOne] =
                ((refParams.view zip byRefArgs.view.map(_.refersTo)) ++
                  (mpcalProcedure.variables.view zip transformedVariables) ++
                  (transformedValParams.view zip transformedValParams) ++
                  View(mpcalProcedure.selfDecl -> freshSelfDecl))
                  .to(ById.mapFactory)

              // apply substitutions before applying mapping macros, so that mapping macros are checked against the
              // names we know, not any intermediate ref-names.
              generatedPCalProcedures +=
                PCalProcedure(
                  freshName, freshSelfDecl, transformedValParams, transformedVariables,
                  mpcalProcedure.body.view
                    .map(applySubstitutions(_)(substitutions = substitutions))
                    .flatMap(applyMappingMacros(_)(mappingsMap = mappingsMap, selfDecl = freshSelfDecl))
                    .toList)

              // for any recursions we encountered
              recursionFixList.foreach(_(generatedPCalProcedures.last))

              generatedPCalProcedures.last
            })

            cacheRecord match {
              case Left((freshName, recList)) =>
                val result = PCalCall(freshName, byValueArgs)
                recList += result.setRefersTo // will be called "later", once the procedure we refer to is constructed
                result
              case Right(target) =>
                PCalCall(target.name, byValueArgs)
                  .setRefersTo(target)
            }
          case stmt => updateReads(stmt)
        }
        stmtSink(List(unwrappedStmt))
      }

      // for many-to-one archetype params, we have to:
      // 1. duplicate references to the parameter, so, if each one has a different mapping, that is respected
      // 2. deduplicate references pcal-wide, once mappings have been applied
      // .. so, this map accumulates these extra deduplicating repairs for later execution
      val repairSubstitutions = mutable.HashMap[ById[RefersTo.HasReferences],DefinitionOne]()

      // TODO: single-process MPCal
      val rewritten = block.rewrite(Rewritable.TopDownFirstStrategy) {
        case instance @MPCalInstance(selfDecl, fairness, archetypeName, arguments, mappings) =>
          val archetype = instance.refersTo

          val substitutionsBuilder = mutable.Buffer.empty[(RefersTo.HasReferences,DefinitionOne)]
          val variables = archetype.variables.iterator.map { v =>
            // clean state var names, so that we don't add state variable naming conflicts during expansion
            val clone = v match {
              case PCalVariableDeclarationEmpty(name) =>
                PCalVariableDeclarationEmpty(TLAIdentifier(stateVarNameCleaner.cleanName(name.id)))
              case PCalVariableDeclarationValue(name, value) =>
                PCalVariableDeclarationValue(TLAIdentifier(stateVarNameCleaner.cleanName(name.id)), value)
              case PCalVariableDeclarationSet(name, set) =>
                PCalVariableDeclarationSet(TLAIdentifier(stateVarNameCleaner.cleanName(name.id)), set)
            }
            substitutionsBuilder += v -> clone
            clone
          }.to(mutable.ListBuffer)

          val refArgsSeen = mutable.HashSet[ById[DefinitionOne]]()
          (arguments.iterator zip archetype.params).foreach {
            case Left(arg @MPCalRefExpr(_, _)) -> param =>
              if(refArgsSeen(ById(arg.refersTo))) {
                val freshArgRef = PCalVariableDeclarationEmpty(arg.refersTo.identifier.asInstanceOf[ScopeIdentifierName].name)
                repairSubstitutions += ById(freshArgRef) -> arg.refersTo
                substitutionsBuilder += param -> freshArgRef
              } else {
                refArgsSeen += ById(arg.refersTo)
                substitutionsBuilder += param -> arg.refersTo
              }
            case Right(expr) -> param =>
              // expr might contain references to the process's ID alias. replace them with "self" ids,
              // still referring to selfDecl, so that the generated PlusCal just contains references to "self" in the right place(s)
              variables += PCalVariableDeclarationValue(TLAIdentifier(stateVarNameCleaner.cleanName(param.name.id)), expr.rewrite(Rewritable.TopDownFirstStrategy) {
                case ident@TLAGeneralIdentifier(_, _) if ident.refersTo eq selfDecl =>
                  TLAGeneralIdentifier(TLAIdentifier("self"), Nil)
                    .setRefersTo(selfDecl)
              })
              substitutionsBuilder += param -> variables.last
          }
          val substitutions = substitutionsBuilder.to(ById.mapFactory)

          val mappingsMap = mappings.iterator.map {
            case mapping @MPCalMapping(MPCalMappingTarget(index, mappingCount), _) =>
              val param = archetype.params(index)
              substitutions(ById(param)) -> (mappingCount, mapping.refersTo)
          }.to(ById.mapFactory)

          generatedPCalProcesses += PCalProcess(
            selfDecl, fairness, variables.result(),
            archetype.body.view
              .map(applySubstitutions(_)(substitutions = substitutions))
              .flatMap(applyMappingMacros(_)(mappingsMap = mappingsMap, selfDecl = selfDecl))
              .toList
          ).setSourceLocation(instance.sourceLocation)

          instance // return the instance unchanged; we got what we came for
        case proc@PCalProcess(selfDecl, fairness, variables, body) =>
          proc.withChildren(Iterator(selfDecl, fairness, variables,
            body.flatMap(applyMappingMacros(_)(mappingsMap = Map.empty, selfDecl = selfDecl))))
        case proc@PCalProcedure(name, selfDecl, params, variables, body) =>
          proc.withChildren(Iterator(name, selfDecl, params, variables,
            body.flatMap(applyMappingMacros(_)(mappingsMap = Map.empty, selfDecl = selfDecl))))
      }

      val pcalAlgorithm = rewritten.copy(
        pcalProcedures = rewritten.pcalProcedures ++ generatedPCalProcedures.result(),
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

      // as mentioned above, repair any duplicate definitions once everything is expanded
      val pcalAlgorithmRepaired = applySubstitutions(pcalAlgorithm)(substitutions = repairSubstitutions.toMap)
      pcalAlgorithmRepaired
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
            case PCalAssignmentLhsIdentifier(_) => keysAcc.result().reverse
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
      final implicit class CountOps(val self: Map[ById[DefinitionOne],Int]) {
        def +++(other: Map[ById[DefinitionOne],Int]): Map[ById[DefinitionOne],Int] =
          (self.keysIterator ++ other.keysIterator).map { defnId =>
            defnId -> (self.getOrElse(defnId, 0) + other.getOrElse(defnId, 0))
          }.toMap

        def |||(other: Map[ById[DefinitionOne],Int]): Map[ById[DefinitionOne],Int] =
          (self.keysIterator ++ other.keysIterator).map { defnId =>
            defnId -> (self.getOrElse(defnId, 0) max other.getOrElse(defnId, 0))
          }.toMap
      }

      block.rewrite(Rewritable.TopDownFirstStrategy) {
        case labeledStmts@PCalLabeledStatements(label, body) =>
          // build a lazy system for counting assignments within trees of statements: any statement + list of statements
          // should be traversed at most once, then the result should be cached in these tables.
          // Note: this has to be done with lazy evals, as opposed to pre-computation, because parts of this code generate
          //       ad-hoc fresh ASTs during rewriting. You can't pre-compute ad-hoc future data.
          var assignmentCountsStmtMap = Map.empty[ById[PCalStatement],Map[ById[DefinitionOne],Int]]
          var assignmentCountsMap = Map.empty[ById[List[PCalStatement]],Map[ById[DefinitionOne],Int]]

          def assignmentCountsStmt(stmt: PCalStatement): Map[ById[DefinitionOne],Int] =
            assignmentCountsStmtMap.getOrElse(ById(stmt), {
              var result = Map.empty[ById[DefinitionOne],Int]
              stmt.visit(Visitable.TopDownFirstStrategy) {
                case stmt: PCalStatement if assignmentCountsStmtMap.contains(ById(stmt)) =>
                  result +++= assignmentCountsStmtMap(ById(stmt))
                case PCalIf(_, yes, no) =>
                  result +++= (assignmentCounts(yes) ||| assignmentCounts(no))
                case PCalEither(cases) =>
                  result +++= cases.iterator.map(assignmentCounts).reduce(_ ||| _)
                case PCalAssignment(List(PCalAssignmentPair(lhs: PCalAssignmentLhsIdentifier, _))) =>
                  result = result.updated(ById(lhs.refersTo), result.getOrElse(ById(lhs.refersTo), 0) + 1)
              }
              assignmentCountsStmtMap = assignmentCountsStmtMap.updated(ById(stmt), result)
              result
            })

          def assignmentCounts(stmts: List[PCalStatement]): Map[ById[DefinitionOne],Int] =
            assignmentCountsMap.getOrElse(ById(stmts), {
              val result = stmts match {
                case Nil => Map.empty[ById[DefinitionOne],Int]
                case hd :: tl => assignmentCountsStmt(hd) +++ assignmentCounts(tl)
              }
              assignmentCountsMap = assignmentCountsMap.updated(ById(stmts), result)
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

          def impl(stmts: List[PCalStatement], substitutions: Map[ById[DefinitionOne],DefinitionOne], lifted: List[DefinitionOne]): List[PCalStatement] = {
            /**
             * Perform substitutions, _specifically avoiding assignment LHS_! Fundamentally, these subs are for
             * temporary with-bindings, and they should never change an assignment target.
             *
             * "Adding the LHS case in the hope it would fix something, only to break something" count of shame: 1, pre-comment
             */
            def performSubstitutions[T <: Rewritable](node: T, substitutions: Map[ById[DefinitionOne],DefinitionOne]): T =
              node.rewrite(Rewritable.BottomUpOnceStrategy) {
                case ident@TLAGeneralIdentifier(_, pfx) if substitutions.contains(ById(ident.refersTo)) =>
                  assert(pfx.isEmpty)
                  // substitution just once is fine in this use case, because we will always update the intended substitution
                  // to the latest one possible (e.g the map will not contain transitive substitutions)
                  val sub = substitutions(ById(ident.refersTo))
                  ident.withChildren(Iterator(sub.identifier.asInstanceOf[Definition.ScopeIdentifierName].name, Nil)).setRefersTo(sub)
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
                lifted.map { liftedFrom =>
                  val liftedTo = substitutions(ById(liftedFrom)) // grab the most up to date binding this was lifted to
                  PCalAssignment(List(PCalAssignmentPair(
                    PCalAssignmentLhsIdentifier(liftedFrom.identifier.asInstanceOf[Definition.ScopeIdentifierName].name).setRefersTo(liftedFrom),
                    TLAGeneralIdentifier(liftedTo.identifier.asInstanceOf[Definition.ScopeIdentifierName].name, Nil).setRefersTo(liftedTo),
                  )))
                } ::: tailStmts.mapConserve(performSubstitutions(_, substitutions)) // make sure call args get replaced, because they might use with-bound names that have changed
              case Nil => !!! // taken care of by TailJumpStmts, but scalac doesn't know that
              case hd :: tl =>
                hd match {
                  case PCalAssignment(List(PCalAssignmentPair(lhs: PCalAssignmentLhsIdentifier, rhs))) if assignmentCounts(tl).getOrElse(ById(lhs.refersTo), 0) >= 1 =>
                    val rebind = PCalVariableDeclarationValue(TLAIdentifier(nameCleaner.cleanName(lhs.identifier.id)), performSubstitutions(rhs, substitutions))
                    val newLifted = {
                      // only add to lifted if we haven't seen this kind of assignment before
                      if(!substitutions.contains(ById(lhs.refersTo))) lhs.refersTo :: lifted else lifted
                    }
                    List(PCalWith(List(rebind),
                      impl(tl, substitutions.updated(ById(lhs.refersTo), rebind), newLifted)
                    ))
                  case stmt@PCalAssignment(List(PCalAssignmentPair(lhs: PCalAssignmentLhsIdentifier, rhs))) if assignmentCounts(tl).getOrElse(ById(lhs.refersTo), 0) == 0 =>
                    // if this was the last assignment, leave it intact, and remove data that would have a second "last assignment" generated at end of block
                    PCalAssignment(List(PCalAssignmentPair(lhs, performSubstitutions(rhs, substitutions)))) ::
                      impl(tl, substitutions - ById(lhs.refersTo), lifted.filter(_ ne lhs.refersTo))
                  case PCalWith(bindings, body) if tl.isEmpty =>
                    val transformedBindings = bindings.mapConserve(performSubstitutions(_, substitutions))
                    List(PCalWith(transformedBindings,
                      impl(body, substitutions ++ (bindings.view.map(ById(_)) zip transformedBindings).filter(p => p._1.ref ne p._2), lifted)))
                  case PCalWith(bindings, body) =>
                    var nextSubstitutions = substitutions
                    // push the remaining statements inside the body, so lifted assignments are guaranteed to be in scope
                    // for the entire critical section. to avoid name collisions, conservatively rename all bindings to fresh names
                    // additional note: be sure to substitute earlier bindings into later bindings!
                    val renamedBindings = bindings.map { decl =>
                      val result = decl match {
                        case PCalVariableDeclarationValue(name, value) =>
                          PCalVariableDeclarationValue(TLAIdentifier(nameCleaner.cleanName(name.id)),
                            performSubstitutions(value, nextSubstitutions))
                        case PCalVariableDeclarationSet(name, set) =>
                          PCalVariableDeclarationSet(TLAIdentifier(nameCleaner.cleanName(name.id)),
                            performSubstitutions(set, nextSubstitutions))
                      }
                      nextSubstitutions = nextSubstitutions.updated(ById(decl), result)
                      result
                    }
                    List(PCalWith(renamedBindings,
                      impl(body ::: tl, nextSubstitutions, lifted)))
                  case PCalIf(cond, yes, no) =>
                    List(PCalIf(
                      performSubstitutions(cond, substitutions),
                      impl(jumpAwareConcat(yes, tl), substitutions, lifted),
                      impl(jumpAwareConcat(no, tl), substitutions, lifted)))
                  case PCalEither(cases) =>
                    List(PCalEither(cases.map(cse => impl(jumpAwareConcat(cse, tl), substitutions, lifted))))
                  case stmt =>
                    performSubstitutions(stmt, substitutions) :: impl(tl, substitutions, lifted)
                }
            }
          }

          labeledStmts.withChildren(Iterator(label, impl(body, Map.empty, Nil)))
      }
    }

    // clean up nested with statements where possible. this is not strictly necessary, but it makes the output code a lot prettier...
    block = locally {
      object NestedWiths {
        @tailrec
        private def impl(stmts: List[PCalStatement], acc: mutable.ListBuffer[List[PCalVariableDeclarationBound]]): Option[(List[List[PCalVariableDeclarationBound]],List[PCalStatement])] =
          stmts match {
            case List(PCalWith(variables, body)) =>
              acc += variables
              impl(body, acc)
            case _ if acc.size > 1 =>
              Some((acc.result(), stmts))
            case _ =>
              None
          }

        def unapply(obj: Any): Option[(List[List[PCalVariableDeclarationBound]],List[PCalStatement])] =
          obj match {
            case PCalWith(variables, body) =>
              impl(body, mutable.ListBuffer(variables))
            case _ => None
          }
      }

      lazy val rewriter: PartialFunction[Rewritable,Rewritable] = {
        case NestedWiths(declss, body) =>
          PCalWith(declss.flatten, body.mapConserve(_.rewrite(Rewritable.TopDownFirstStrategy)(rewriter)))
      }

      block.rewrite(Rewritable.TopDownFirstStrategy)(rewriter)
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
