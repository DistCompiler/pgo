package pgo.util

import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite
import pgo.model.SourceLocation
import pgo.model.tla.BuiltinModules
import pgo.parser.TLAParser
import pgo.trans.MPCalGoCodegenPass
import pgo.util.TLAExprInterpreter._

import scala.util.{Failure, Success}

class TLAExprInterpreterTests extends AnyFunSuite {
  private lazy val builtinOps = BuiltinModules.builtinModules.values.view
    .flatMap(_.members)
    .filter(op => !MPCalGoCodegenPass.unsupportedOperators(ById(op)))
    .toList

  def checkPass(name: String)(pair: (String,TLAValue))(implicit pos: Position): Unit = {
    val (str, expectedValue) = pair
    checkMultiPass(name)((str, Set(expectedValue)))
  }

  def checkMultiPass(name: String)(pair: (String,Set[TLAValue]))(implicit pos: Position): Unit = {
    test(name) {
      val (str, expectedValues) = pair
      val expr = TLAParser.readExpression(new SourceLocation.UnderlyingString(str), str, definitions = builtinOps)
      val actualValues = TLAExprInterpreter.interpret(expr)(Map.empty).outcomes.map {
        case Success(value) => value
        case Failure(exception) => throw exception
      }.toSet
      assert(actualValues == expectedValues)
    }
  }

  def checkTypeError(name: String)(str: String)(implicit pos: Position): Unit = {
    test(name) {
      val expr = TLAParser.readExpression(new SourceLocation.UnderlyingString(str), str, definitions = builtinOps)
      assertThrows[TLAExprInterpreter.TypeError] {
        TLAExprInterpreter.interpret(expr)(Map.empty)
          .assumeUnambiguousSuccess
      }
    }
  }

  checkTypeError("pow function overflow") {
    raw"""48 ^ 37"""
  }

  checkPass("function call, arg in domain") {
    raw"""[foo |-> 1]["foo"]""" -> TLAValueNumber(1)
  }

  checkTypeError("function call, arg outside domain") {
    raw"""[foo |-> 1]["bar"]"""
  }

  checkPass("existential avoids errors when a set is empty") {
    raw"""\E <<w, zk>> \in {"}nWO"}, juAOg \in {} : w""" -> TLAValueBool(false)
  }

  checkPass("dot operator with spaces around the `.`") {
    raw"""[x |-> 1] . x""" -> TLAValueNumber(1)
  }

  checkPass("function application with a space before the `[`") {
    raw"""[x |-> 1] ["x"]""" -> TLAValueNumber(1)
  }

  checkPass("cross product, expected case") {
    raw"""{1, 2} \X {3, 4} \X {5}""" -> TLAValueSet(Set(
      TLAValueTuple(Vector(TLAValueNumber(1), TLAValueNumber(3), TLAValueNumber(5))),
      TLAValueTuple(Vector(TLAValueNumber(1), TLAValueNumber(4), TLAValueNumber(5))),
      TLAValueTuple(Vector(TLAValueNumber(2), TLAValueNumber(3), TLAValueNumber(5))),
      TLAValueTuple(Vector(TLAValueNumber(2), TLAValueNumber(4), TLAValueNumber(5))),
    ))
  }

  checkMultiPass("CHOOSE multi-value semantics") {
    raw"""CHOOSE x \in {1, 2, 3} : x > 1""" -> Set(TLAValueNumber(2), TLAValueNumber(3))
  }

  checkTypeError("CHOOSE when no value is available") {
    raw"""CHOOSE x \in {1, 2, 3} : x = 4"""
  }

  checkMultiPass("CHOOSE as nested expression") {
    raw"""(CHOOSE x \in {1, 2, 3} : x > 1) + 20""" -> Set(TLAValueNumber(22), TLAValueNumber(23))
  }

  checkPass("ensure we do tuple indexing right by a strong example") {
    s"""{[asZX9CzCt25kR |-> IsFiniteSet({}), wMuDL7vAxos |-> Zero, u8CCtjXS4Qm1QQWq7B |-> fUvEkcAMZ1klHtG6, i |-> Zero]
       |: <<fUvEkcAMZ1klHtG6, c94gDDm, hfc>> \\in Seq({<<>>, Zero, {}})}""".stripMargin ->
      TLAValueSet(Set(TLAValueFunction(Map(TLAValueString("asZX9CzCt25kR") -> TLAValueBool(true), TLAValueString("wMuDL7vAxos") -> TLAValueNumber(0), TLAValueString("u8CCtjXS4Qm1QQWq7B") -> TLAValueTuple(Vector()), TLAValueString("i") -> TLAValueNumber(0))), TLAValueFunction(Map(TLAValueString("asZX9CzCt25kR") -> TLAValueBool(true), TLAValueString("wMuDL7vAxos") -> TLAValueNumber(0), TLAValueString("u8CCtjXS4Qm1QQWq7B") -> TLAValueSet(Set()), TLAValueString("i") -> TLAValueNumber(0))), TLAValueFunction(Map(TLAValueString("asZX9CzCt25kR") -> TLAValueBool(true), TLAValueString("wMuDL7vAxos") -> TLAValueNumber(0), TLAValueString("u8CCtjXS4Qm1QQWq7B") -> TLAValueNumber(0), TLAValueString("i") -> TLAValueNumber(0)))))
  }

  checkPass("creating a set with elements that have different types") {
    s"""{Zero, {}, 3, <<{}>>, {}, {}, IsFiniteSet({}), <<<<>>>>}""" ->
      TLAValueSet(Set(TLAValueNumber(0), TLAValueTuple(Vector(TLAValueSet(Set()))), TLAValueNumber(3),
        TLAValueTuple(Vector(TLAValueTuple(Vector()))), TLAValueSet(Set()), TLAValueBool(true)))
  }

  checkTypeError("out of bounds SubSeq 1") {
    raw"""SubSeq(<<1, 2, 3>>, 1, 4)"""
  }

  checkTypeError("out of bounds SubSeq 2") {
    raw"""SubSeq(<<1, 2, 3>>, 0, 3)"""
  }

  checkPass("identity SubSeq") {
    raw"""SubSeq(<<1, 2, 3>>, 1, 3)""" -> TLAValueTuple(Vector(TLAValueNumber(1), TLAValueNumber(2), TLAValueNumber(3)))
  }

  checkPass("function defn short-circuits on empty set") {
    raw"""[<<foo, bar>> \in {12}, y \in {} |-> bar]""" -> TLAValueFunction(Map.empty)
  }

  checkTypeError("function defn fails with incompatible indices") {
    raw"""[<<foo, bar>> \in {12} |-> bar]"""
  }

  checkPass("modulo") {
    raw"""82 % 39""" -> TLAValueNumber(4)
  }

  checkTypeError("modulo with negative") {
    raw"""82 % -39"""
  }

  checkPass("short-circuiting AND") {
    raw"""/\ FALSE
         |/\ Assert(FALSE, "boom")""".stripMargin -> TLAValueBool(false)
  }

  checkPass("short-circuiting OR") {
    raw"""\/ TRUE
         |\/ Assert(FALSE, "boom")""".stripMargin -> TLAValueBool(true)
  }

  checkPass("short-circuiting logical implication") {
    raw"""FALSE => Assert(FALSE, "boom")""" -> TLAValueBool(true)
  }
}
