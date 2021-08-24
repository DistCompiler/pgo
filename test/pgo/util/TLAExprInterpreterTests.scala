package pgo.util

import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite
import pgo.model.SourceLocation
import pgo.model.tla.BuiltinModules
import pgo.parser.TLAParser
import pgo.trans.MPCalGoCodegenPass
import pgo.util.TLAExprInterpreter.{TLAValue, TLAValueBool, TLAValueFunction, TLAValueNumber, TLAValueSet, TLAValueString, TLAValueTuple}

import scala.collection.immutable.HashSet

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

  checkPass("existential avoids errors when a set is empty") {
    s"""\\E <<w, zk>> \\in {"}nWO"}, juAOg \\in {} : w""" -> TLAValueBool(false)
  }

  checkPass("ensure we do tuple indexing right by a strong example") {
    s"""{[asZX9CzCt25kR |-> IsFiniteSet({}), wMuDL7vAxos |-> Zero, u8CCtjXS4Qm1QQWq7B |-> fUvEkcAMZ1klHtG6, i |-> Zero]
       |: <<fUvEkcAMZ1klHtG6, c94gDDm, hfc>> \\in Seq({<<>>, Zero, {}})}""".stripMargin ->
      TLAValueSet(Set(TLAValueFunction(Map(TLAValueString("asZX9CzCt25kR") -> TLAValueBool(true), TLAValueString("wMuDL7vAxos") -> TLAValueNumber(0), TLAValueString("u8CCtjXS4Qm1QQWq7B") -> TLAValueTuple(Vector()), TLAValueString("i") -> TLAValueNumber(0))), TLAValueFunction(Map(TLAValueString("asZX9CzCt25kR") -> TLAValueBool(true), TLAValueString("wMuDL7vAxos") -> TLAValueNumber(0), TLAValueString("u8CCtjXS4Qm1QQWq7B") -> TLAValueSet(Set()), TLAValueString("i") -> TLAValueNumber(0))), TLAValueFunction(Map(TLAValueString("asZX9CzCt25kR") -> TLAValueBool(true), TLAValueString("wMuDL7vAxos") -> TLAValueNumber(0), TLAValueString("u8CCtjXS4Qm1QQWq7B") -> TLAValueNumber(0), TLAValueString("i") -> TLAValueNumber(0)))))
  }

  checkPass("creating a set with elements that have different types") {
    s"""{Zero, {}, 3, <<{}>>, {}, {}, IsFiniteSet({}), <<<<>>>>}""" ->
      TLAValueSet(HashSet(TLAValueNumber(0), TLAValueTuple(Vector(TLAValueSet(Set()))), TLAValueNumber(3),
        TLAValueTuple(Vector(TLAValueTuple(Vector()))), TLAValueSet(Set()), TLAValueBool(true)))
  }
}
