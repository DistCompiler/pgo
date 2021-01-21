package pgo

import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite
import pgo.model.tla.TLAExpression
import pgo.model.tla.TLABuilder._

import scala.jdk.CollectionConverters._

class ExpressionCodeGenRunFailureTest extends AnyFunSuite {
  def check(tag: String)(expr: TLAExpression, vars: List[IntegrationTestingUtils.KeyValue], expected: String)(implicit pos: Position): Unit =
    test(tag) {
      IntegrationTestingUtils.testCompileExpression(expr, vars.asJava, { outputPath =>
        IntegrationTestingUtils.testRunGoCodeShouldPanic(outputPath, expected.linesIterator.toList.asJava)
      })
    }

  check("unsatisfiable case expr")(
    expr=caseexp(arms(arm(bool(false), str("Hello world"))), null),
    vars=Nil,
    "panic: No matching case!")
}