package pgo.trans

import pgo.model.{PGoError, Rewritable}
import pgo.model.mpcal._
import pgo.model.pcal._
import pgo.model.tla._
import pgo.util.{MPCalPassUtils, NameCleaner}

import scala.annotation.tailrec

object MPCalNormalizePass {
  @throws[PGoError]
  def apply(tlaModule: TLAModule, mpcalBlock: MPCalBlock): MPCalBlock = {
    // remove while loops
    var block: MPCalBlock = mpcalBlock.rewrite(Rewritable.BottomUpOnceStrategy) {
      case labeledStmts @PCalLabeledStatements(label, (whileStmt @PCalWhile(condition, body)) :: restStmts) =>
        PCalLabeledStatements(
          label,
          PCalIf(
            condition,
            body :+ PCalGoto(label.name).setSourceLocation(whileStmt.sourceLocation),
            Nil).setSourceLocation(whileStmt.sourceLocation) :: restStmts)
          .setSourceLocation(labeledStmts.sourceLocation)
    }

    block = MPCalPassUtils.rewriteEachBody(block) { (body, lexicalScope) =>
      MPCalPassUtils.expandMacroCalls(body, lexicalScope)
    }

    val nameCleaner = new NameCleaner
    MPCalPassUtils.forEachName(tlaModule, block)(nameCleaner.addKnownName)

    // remove multiple assignment
    block = MPCalPassUtils.rewriteEachBody(block) { (body, _) =>
      def impl(body: List[PCalStatement]): List[PCalStatement] =
        body.flatMap {
          case PCalAssignment(pairs) if pairs.size > 1 =>
            @tailrec
            def lhsIdentifier(lhs: PCalAssignmentLhs): TLAIdentifier =
              lhs match {
                case PCalAssignmentLhsIdentifier(identifier) => identifier
                case PCalAssignmentLhsProjection(lhs, _) => lhsIdentifier(lhs)
                case PCalAssignmentLhsExtension(contents) => ???
              }
            val bindings = pairs.map {
              case pair @PCalAssignmentPair(lhs, rhs) =>
                val lhsIdent = lhsIdentifier(lhs)
                val lhsName = nameCleaner.cleanName(lhsIdent.id)
                PCalVariableDeclarationValue(lhsIdent.withChildren(Iterator(lhsName)), rhs)
                  .setSourceLocation(pair.sourceLocation)
            }
            pairs.map {
              case pair @PCalAssignmentPair(lhs, rhs) =>
                PCalAssignment(List(???))
            }
          case stmt @PCalEither(cases) =>
            List(stmt.withChildren(Iterator(cases.mapConserve(impl))))
          case stmt @PCalIf(condition, yes, no) =>
            List(stmt.withChildren(Iterator(
              condition, impl(yes), impl(no))))
          case stmt @PCalLabeledStatements(label, statements) =>
            List(stmt.withChildren(Iterator(
              label, impl(statements))))
          case stmt @PCalWhile(condition, body) =>
            List(stmt.withChildren(Iterator(
              condition, impl(body))))
          case stmt @PCalWith(variables, body) =>
            List(stmt.withChildren(Iterator(
              variables, impl(body))))
        }

      impl(body)
    }

    block
  }
}
