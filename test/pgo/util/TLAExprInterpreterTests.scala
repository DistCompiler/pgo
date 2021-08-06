package pgo.util

import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite
import pgo.model.SourceLocation
import pgo.model.tla.BuiltinModules
import pgo.parser.TLAParser
import pgo.trans.MPCalGoCodegenPass
import pgo.util.TLAExprInterpreter.{TLAValue, TLAValueNumber}

class TLAExprInterpreterTests extends AnyFunSuite {
  private lazy val builtinOps = BuiltinModules.builtinModules.values.view
    .flatMap(_.members)
    .filter(op => !MPCalGoCodegenPass.unsupportedOperators(op))
    .toList

  def checkPass(name: String)(pair: (String,TLAValue))(implicit pos: Position): Unit = {
    test(name) {
      val (str, expectedValue) = pair
      val expr = TLAParser.readExpression(new SourceLocation.UnderlyingString(str), str, definitions = builtinOps)
      val actualValue = TLAExprInterpreter.interpret(expr)(Map.empty)
      assert(actualValue == expectedValue)
    }
  }

  def checkTypeError(name: String)(str: String)(implicit pos: Position): Unit = {
    test(name) {
      val expr = TLAParser.readExpression(new SourceLocation.UnderlyingString(str), str, definitions = builtinOps)
      assertThrows[TLAExprInterpreter.TypeError] {
        TLAExprInterpreter.interpret(expr)(Map.empty)
      }
    }
  }

  checkPass("function call, arg in domain") {
    s"""[foo |-> 1]["foo"]""" -> TLAValueNumber(1)
  }

  checkTypeError("function call, arg outside domain") {
    s"""[foo |-> 1]["bar"]"""
  }

}
