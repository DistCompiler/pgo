package pgo.trans

import scala.annotation.tailrec

import pgo.model.mpcal.*
import pgo.model.pcal.*
import pgo.model.tla.*
import pgo.model.{
  DerivedSourceLocation,
  PGoError,
  Rewritable,
  SourceLocationInternal,
  Visitable,
}
import pgo.util.{!!!, ById, Description, MPCalPassUtils, NameCleaner}

import Description.*

object MPCalNormalizePass {
  @throws[PGoError]
  def apply(tlaModule: TLAModule, mpcalBlock: MPCalBlock): MPCalBlock = {
    var block: MPCalBlock = mpcalBlock

    // expand all PCal macros (not including archetypes + mapping macros)
    block = MPCalPassUtils.rewriteEachBody(block) { (body, lexicalScope) =>
      MPCalPassUtils.expandMacroCalls(body, lexicalScope)
    }
    // remove the now-expanded macros
    locally {
      val stableBlock =
        block // hax because decorateLike incorrectly uses this.type
      block = stableBlock.decorateLike(
        stableBlock.copy(macros = Nil).asInstanceOf[stableBlock.type],
      )
    }

    // normalise label nesting, so all labels appear at the top level.
    // retain control flow by injecting synthetic gotos at label boundaries that use fall-through
    // do this as early as possible (minus PCal macros), as it helps other passes skip nested label-related edge cases:
    //   it is very useful to have the guarantee that some syntactically nested compound statement must be entirely
    //   within the same critical section (and, in some cases, to know that syntactically all sub-statements will not involve labels)
    block = locally {
      val containsLabels = MPCalPassUtils.gatherContainsLabels(block)

      // labelAfter will be used as target for any synthetic jumps inserted when control flow would otherwise "run off the end"
      //   this varies depending on whether we're in a procedure or process (Done and Error, respectively)
      def rewriteBody(
          body: List[PCalStatement],
          labelAfter: PCalLabel,
      ): List[PCalStatement] = {
        def findLabelAfter(
            restStmts: List[PCalStatement],
            labelAfter: Option[PCalLabel],
        ): Option[PCalLabel] =
          restStmts match {
            case Nil                                  => labelAfter
            case PCalLabeledStatements(label, _) :: _ => Some(label)
            case _                                    => None
          }

        @tailrec
        def transBlocks(
            blocks: List[PCalLabeledStatements],
            labelAfter: Option[PCalLabel],
            blocksOut: Iterator[PCalLabeledStatements],
        ): Iterator[PCalLabeledStatements] =
          blocks match {
            case Nil => blocksOut
            case (labeledStmts @ PCalLabeledStatements(
                  whileLabel,
                  (whileStmt @ PCalWhile(
                    whileCondition,
                    whileBody,
                  )) :: afterWhileStmts,
                )) :: restBlocks =>
              val (whileBodyTrans, whileBodyBlocks) = impl(
                whileBody,
                Some(whileLabel),
                Iterator.empty,
                Iterator.empty,
              )
              val (afterWhileTrans, afterWhileBlocks) = impl(
                afterWhileStmts,
                findLabelAfter(restBlocks, labelAfter),
                Iterator.empty,
                Iterator.empty,
              )
              val whileTrans =
                PCalIf(whileCondition, whileBodyTrans, afterWhileTrans)
                  .setSourceLocation(whileStmt.sourceLocation)
              val labeledStmtsTrans = labeledStmts.withChildren(
                Iterator(whileLabel, whileTrans :: Nil),
              )
              transBlocks(
                restBlocks,
                labelAfter,
                blocksOut ++ Iterator.single(
                  labeledStmtsTrans,
                ) ++ whileBodyBlocks ++ afterWhileBlocks,
              )
            case (labeledStmts @ PCalLabeledStatements(
                  label,
                  stmts,
                )) :: restBlocks =>
              val (stmtsTrans, stmtsBlocks) = impl(
                stmts,
                findLabelAfter(restBlocks, labelAfter),
                Iterator.empty,
                Iterator.empty,
              )
              val labeledTrans =
                labeledStmts.withChildren(Iterator(label, stmtsTrans))
              transBlocks(
                restBlocks,
                labelAfter,
                blocksOut ++ Iterator.single(labeledTrans) ++ stmtsBlocks,
              )
          }

        def transStmt(
            stmt: PCalStatement,
            labelAfter: Option[PCalLabel],
        ): (PCalStatement, Iterator[PCalLabeledStatements]) =
          stmt match {
            case stmt @ PCalEither(cases) =>
              val casesTrans =
                cases.map(impl(_, labelAfter, Iterator.empty, Iterator.empty))
              (
                stmt.withChildren(Iterator(casesTrans.map(_._1))),
                casesTrans.iterator.flatMap(_._2),
              )
            case stmt @ PCalIf(condition, yes, no) =>
              val (yesTrans, yesBlocks) =
                impl(yes, labelAfter, Iterator.empty, Iterator.empty)
              val (noTrans, noBlocks) =
                impl(no, labelAfter, Iterator.empty, Iterator.empty)
              (
                stmt.withChildren(Iterator(condition, yesTrans, noTrans)),
                yesBlocks ++ noBlocks,
              )
            case PCalLabeledStatements(_, _) =>
              !!! // should be inaccessible; handled via other cases
            case PCalWhile(_, _) => !!! // see above
            case stmt @ PCalWith(variables, body) =>
              val (bodyTrans, bodyBlocks) =
                impl(body, labelAfter, Iterator.empty, Iterator.empty)
              assert(bodyBlocks.isEmpty)
              (
                stmt.withChildren(Iterator(variables, bodyTrans)),
                Iterator.empty,
              )
            case stmt => (stmt, Iterator.empty)
          }

        def impl(
            stmts: List[PCalStatement],
            labelAfter: Option[PCalLabel],
            stmtsOut: Iterator[PCalStatement],
            blocksOut: Iterator[PCalLabeledStatements],
        ): (List[PCalStatement], Iterator[PCalLabeledStatements]) = {
          object ContainsJump {
            def unapply(
                stmts: List[PCalStatement],
            ): Option[(List[PCalStatement], List[PCalStatement], Boolean)] =
              stmts match {
                case (goto: PCalGoto) :: restBlocks =>
                  Some((List(goto), restBlocks, false))
                case (ret: PCalReturn) :: restBlocks =>
                  Some((List(ret), restBlocks, false))
                case (ifStmt: PCalIf) :: restBlocks
                    if containsLabels(ById(ifStmt)) =>
                  Some((List(ifStmt), restBlocks, false))
                case (either: PCalEither) :: restBlocks
                    if containsLabels(ById(either)) =>
                  Some((List(either), restBlocks, false))

                case (call: PCalCall) :: (ret: PCalReturn) :: restBlocks =>
                  Some((List(call, ret), restBlocks, false))
                case (call: PCalCall) :: (goto: PCalGoto) :: restBlocks =>
                  Some((List(call, goto), restBlocks, false))
                case (call: PCalCall) :: restBlocks =>
                  Some((List(call), restBlocks, true))

                case (mpCall @ PCalExtensionStatement(
                      _: MPCalCall,
                    )) :: (ret: PCalReturn) :: restBlocks =>
                  Some((List(mpCall, ret), restBlocks, false))
                case (mpCall @ PCalExtensionStatement(
                      _: MPCalCall,
                    )) :: (goto: PCalGoto) :: restBlocks =>
                  Some((List(mpCall, goto), restBlocks, false))
                case (mpCall @ PCalExtensionStatement(
                      _: MPCalCall,
                    )) :: restBlocks =>
                  Some((List(mpCall), restBlocks, true))

                case _ => None
              }
          }

          stmts match {
            case Nil =>
              val synthJump = labelAfter.map { label =>
                PCalGoto(label.name)
                  .setSourceLocation(
                    DerivedSourceLocation(
                      label.sourceLocation,
                      SourceLocationInternal,
                      d"tail-block transformation",
                    ),
                  )
              }
              ((stmtsOut ++ synthJump.iterator).toList, blocksOut)
            case allBlocks @ PCalLabeledStatements(nextLabel, _) :: _ =>
              assert(allBlocks.forall(_.isInstanceOf[PCalLabeledStatements]))
              val (resultStmts, _) =
                impl(Nil, Some(nextLabel), stmtsOut, Iterator.empty)
              (
                resultStmts,
                transBlocks(
                  allBlocks.asInstanceOf[List[PCalLabeledStatements]],
                  labelAfter,
                  blocksOut,
                ),
              )
            case ContainsJump(jumpStmts, restStmts, needsGoto) =>
              assert(restStmts.forall(_.isInstanceOf[PCalLabeledStatements]))
              val localLabelAfter = findLabelAfter(restStmts, labelAfter)
              val jumpTrans = jumpStmts.map(transStmt(_, localLabelAfter)) :::
                (if (needsGoto) {
                   List((PCalGoto(localLabelAfter.get.name), Iterator.empty))
                 } else Nil)
              (
                (stmtsOut ++ jumpTrans.iterator.map(_._1)).toList,
                transBlocks(
                  restStmts.asInstanceOf[List[PCalLabeledStatements]],
                  labelAfter,
                  blocksOut ++ jumpTrans.iterator.flatMap(_._2),
                ),
              )
            case stmt :: restStmts =>
              val (stmtTrans, stmtBlocks) =
                transStmt(stmt, findLabelAfter(restStmts, labelAfter))
              // if:
              //   1. restStmts is empty, or labeled
              //   2. stmt had sub-statements (proxy: the translation was one of the compound expressions we don't desugar), and we had a labelAfter
              // then stmt will have our final gotos embedded into it, so we should _not_ add our own (which is what will happen if we just recurse on restStmts)
              // otherwise, we recurse normally, and will keep looking for places to add synthetic gotos
              stmtTrans match {
                case PCalEither(_) | PCalIf(_, _, _) | PCalWith(_, _)
                    if restStmts.isEmpty || restStmts.head
                      .isInstanceOf[PCalLabeledStatements] =>
                  assert(
                    restStmts.forall(_.isInstanceOf[PCalLabeledStatements]),
                  )
                  (
                    (stmtsOut ++ Iterator.single(stmtTrans)).toList,
                    transBlocks(
                      restStmts.asInstanceOf[List[PCalLabeledStatements]],
                      labelAfter,
                      blocksOut ++ stmtBlocks,
                    ),
                  )
                case _ =>
                  impl(
                    restStmts,
                    labelAfter,
                    stmtsOut ++ Iterator.single(stmtTrans),
                    blocksOut ++ stmtBlocks,
                  )
              }
          }
        }

        body match {
          case PCalLabeledStatements(_, _) :: _ =>
            assert(body.forall(_.isInstanceOf[PCalLabeledStatements]))
            transBlocks(
              body.asInstanceOf[List[PCalLabeledStatements]],
              Some(labelAfter),
              Iterator.empty,
            ).toList
          case _ =>
            assert(body.forall(stmt => !containsLabels(ById(stmt))))
            body
        }
      }

      block.rewrite(Rewritable.TopDownFirstStrategy) {
        case proc @ MPCalProcedure(name, selfDecl, params, variables, body) =>
          proc.withChildren(
            Iterator(
              name,
              selfDecl,
              params,
              variables,
              rewriteBody(body, PCalLabel("Error", PCalLabel.NoModifier)),
            ),
          )
        case arch @ MPCalArchetype(name, selfDecl, params, variables, body) =>
          arch.withChildren(
            Iterator(
              name,
              selfDecl,
              params,
              variables,
              rewriteBody(body, PCalLabel("Done", PCalLabel.NoModifier)),
            ),
          )
        case proc @ PCalProcedure(name, selfDecl, params, variables, body) =>
          proc.withChildren(
            Iterator(
              name,
              selfDecl,
              params,
              variables,
              rewriteBody(body, PCalLabel("Error", PCalLabel.NoModifier)),
            ),
          )
        case proc @ PCalProcess(selfDecl, fairness, variables, body) =>
          proc.withChildren(
            Iterator(
              selfDecl,
              fairness,
              variables,
              rewriteBody(body, PCalLabel("Done", PCalLabel.NoModifier)),
            ),
          )
      }
    }

    // needed below: gather all names, to generate synthetic ones for multiple assignment temp vars
    val nameCleaner = new NameCleaner
    MPCalPassUtils.forEachName(tlaModule, block)(nameCleaner.addKnownName)
    block.visit(Visitable.BottomUpFirstStrategy) { case ident: TLAIdentifier =>
      nameCleaner.addKnownName(ident.id)
    }

    // desugar multiple assignment into single assignment, using a with statement to ensure correct order of operations
    block = block.rewrite(Rewritable.BottomUpOnceStrategy) {
      case assignment @ PCalAssignment(pairs) if pairs.size > 1 =>
        @tailrec
        def lhsIdentifier(lhs: PCalAssignmentLhs): PCalAssignmentLhsIdentifier =
          (lhs: @unchecked) match {
            case ident @ PCalAssignmentLhsIdentifier(_) => ident
            case PCalAssignmentLhsProjection(lhs, _)    => lhsIdentifier(lhs)
          }
        val bindings = pairs.map { case pair @ PCalAssignmentPair(lhs, rhs) =>
          val lhsIdent = lhsIdentifier(lhs)
          val lhsName = nameCleaner.cleanName(lhsIdent.identifier.id)
          val decl = PCalVariableDeclarationValue(
            TLAIdentifier(lhsName)
              .setSourceLocation(
                lhsIdent.sourceLocation.derivedVia(
                  d"multiple-assignment desugaring",
                ),
              ),
            rhs,
          )
            .setSourceLocation(
              pair.sourceLocation.derivedVia(d"multiple-assignment desugaring"),
            )
          (lhsIdent.refersTo, decl)
        }
        val refMap = bindings.to(ById.mapFactory)
        PCalWith(
          bindings.map(_._2),
          pairs.map { case pair @ PCalAssignmentPair(lhs, rhs) =>
            def applyRenamings[T <: Rewritable](rewritable: T): T =
              rewritable.rewrite(Rewritable.BottomUpOnceStrategy) {
                case ident: TLAGeneralIdentifier
                    if refMap.contains(ById(ident.refersTo)) =>
                  val defn = refMap(ById(ident.refersTo))
                  val loc = ident.sourceLocation.derivedVia(
                    d"multiple-assignment desugaring",
                  )
                  TLAGeneralIdentifier(
                    defn.name.shallowCopy().setSourceLocation(loc),
                    Nil,
                  )
                    .setSourceLocation(loc)
                    .setRefersTo(defn)
              }

            def applyRenamingsToLhs(lhs: PCalAssignmentLhs): PCalAssignmentLhs =
              (lhs: @unchecked) match {
                case ident @ PCalAssignmentLhsIdentifier(_) => ident
                case proj @ PCalAssignmentLhsProjection(lhs, projections) =>
                  proj.withChildren(
                    Iterator(
                      applyRenamingsToLhs(lhs),
                      projections.mapConserve(applyRenamings),
                    ),
                  )
              }

            PCalAssignment(
              List(
                PCalAssignmentPair(
                  applyRenamingsToLhs(lhs),
                  applyRenamings(rhs),
                ),
              ),
            )
              .setSourceLocation(
                pair.sourceLocation.derivedVia(
                  d"multiple-assignment desugaring",
                ),
              )
          },
        )
          .setSourceLocation(
            assignment.sourceLocation.derivedVia(
              d"multiple-assignment desugaring",
            ),
          )
    }

    block
  }
}
