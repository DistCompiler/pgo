package pgo

import org.scalatest.funsuite.AnyFunSuite
import pgo.IntegrationTestingUtils.{KeyValue, testCompileExpression, testRunGoCode}
import pgo.model.tla.TLABuilder._
import pgo.model.tla.TLAExpression

import scala.jdk.CollectionConverters._

class ExpressionCodeGenRunTest extends AnyFunSuite {
  def check(tag: String)(expr: TLAExpression, vars: List[(String,TLAExpression)] = Nil, expectedStr: String): Unit =
    test(tag) {
      // try to run the compiled Go code, check that it prints the right thing
      testCompileExpression(
        expr,
        vars.map(p => new KeyValue(p._1, p._2)).asJava,
        compiledOutputPath =>
          testRunGoCode(compiledOutputPath, expectedStr.linesIterator.toList.asJava))
    }

  check("case expression 3rd case")(
    expr = caseexp(
      arms(
        arm(binop("=", idexp("a"), num(1)), str("a = 1")),
        arm(binop("=", idexp("a"), num(2)), str("a = 2")),
        arm(binop("=", idexp("a"), num(3)), str("a = 3")),
        arm(binop("=", idexp("a"), num(4)), str("a = 4")),
        arm(binop("=", idexp("a"), num(5)), str("a = 5"))),
      str("a > 5 or a < 0")),
    vars = List("a" -> num(3)),
    expectedStr = "a = 3")

  check("case expression default case")(
    expr = caseexp(
      arms(
        arm(binop("=", idexp("a"), num(1)), str("a = 1")),
        arm(binop("=", idexp("a"), num(2)), str("a = 2")),
        arm(binop("=", idexp("a"), num(3)), str("a = 3")),
        arm(binop("=", idexp("a"), num(4)), str("a = 4")),
        arm(binop("=", idexp("a"), num(5)), str("a = 5"))),
      str("a > 5 or a < 0")),
    vars = List("a" -> num(11)),
    expectedStr = "a > 5 or a < 0")

  check("case expression 3rd case no default")(
    expr = caseexp(
      arms(
        arm(binop("=", idexp("a"), num(1)), str("a = 1")),
        arm(binop("=", idexp("a"), num(2)), str("a = 2")),
        arm(binop("=", idexp("a"), num(3)), str("a = 3")),
        arm(binop("=", idexp("a"), num(4)), str("a = 4")),
        arm(binop("=", idexp("a"), num(5)), str("a = 5"))),
      null),
    vars = List("a" -> num(3)),
    expectedStr = "a = 3")

  check("if expression then branch")(
    expr = ifexp(bool(true), str("Then Branch"), str("Else Branch")),
    expectedStr = "Then Branch")

  check("if expression else branch")(
    expr = ifexp(bool(false), str("Then Branch"), str("Else Branch")),
    expectedStr = "Else Branch")

  check("if expression complex then branch")(
    expr = ifexp(binop(">", idexp("a"), idexp("b")), idexp("a"), idexp("b")),
    vars = List("a" -> num(3), "b" -> num(1)),
    expectedStr = "3")

  check("nested if expression else -> then branch")(
    expr = ifexp(bool(false), str("Then Branch"), ifexp(bool(true), str("Else Branch -> Then Branch"), str("Else Branch -> Else Branch"))),
    expectedStr = "Else Branch -> Then Branch")

  check("compound math * (+)")(
    expr = binop("*", idexp("a"), binop("+", idexp("b"), idexp("c"))),
    vars = List("a" -> num(2), "b" -> num(2), "c" -> num(3)),
    expectedStr = "10")

  check("compound math * + *")(
    expr = binop("*", idexp("a"), binop("+", idexp("b"), binop("*", idexp("c"), idexp("c")))),
    vars = List("a" -> num(2), "b" -> num(2), "c" -> num(3)),
    expectedStr = "22")

  check("set enumeration")(
    expr = binop("..", num(0), binop("-", idexp("a"), num(1))),
    vars = List("a" -> num(10)),
    expectedStr = "[0 1 2 3 4 5 6 7 8 9]")

  check("set union no dupes")(
    expr = binop("\\union", idexp("lhs"), idexp("rhs")),
    vars = List(
      "lhs" -> set(num(1), num(2)),
      "rhs" -> set(num(3))),
    expectedStr = "[1 2 3]")

  check("set union with dupes")(
    expr = binop("\\union", idexp("lhs"), idexp("rhs")),
    vars = List(
      "lhs" -> set(num(1), num(2)),
      "rhs" -> set(num(3), num(2))),
    expectedStr = "[1 2 3]")

  check("set diff no intersect")(
    expr = binop("\\", idexp("lhs"), idexp("rhs")),
    vars = List(
      "lhs" -> set(num(1), num(2)),
      "rhs" -> set(num(3))),
    expectedStr = "[1 2]")

  check("set diff intersect")(
    expr = binop("\\", idexp("lhs"), idexp("rhs")),
    vars = List(
      "lhs" -> set(num(1), num(2)),
      "rhs" -> set(num(2))),
    expectedStr = "[1]")

  check("set member check yes")(
    expr = binop("\\in", idexp("x"), idexp("s")),
    vars = List("x" -> num(3), "s" -> set(num(1), num(2), num(3))),
    expectedStr = "true")

  check("set member check no")(
    expr = binop("\\in", idexp("x"), idexp("s")),
    vars = List("x" -> num(30), "s" -> set(num(1), num(3), num(2))),
    expectedStr = "false")

  check("set-of-sets pseudo-lexicographical sorting")(
    idexp("value"),
    vars = List("value" -> set(set(), set(num(1), num(2)), set(num(2)))),
    expectedStr = "[[] [2] [1 2]]")

  check("set-of-tuples pseudo-lexicographical append")(
    idexp("value"),
    vars = List(
      "workaround" -> opcall("Append", tuple(), num(2)),
      "value" -> set(tuple(), tuple(num(1), num(2)), idexp("workaround"))),
    expectedStr = "[[] [2] [1 2]]")

  check("set-of-sets union")(
    expr = binop("\\union", idexp("lhs"), idexp("rhs")),
    vars = List(
      "lhs" -> set(set(num(5), num(3)), set(num(2)), set(num(1), num(10))),
      "rhs" -> set(set(), set(num(2), num(2)))),
    expectedStr = "[[] [2] [1 10] [3 5]]")

  check("set-of-tuples append diff")(
    expr = binop("\\", idexp("lhs"), idexp("rhs")),
    vars = List(
      "workaround1" -> opcall("Append", tuple(), num(1)),
      "workaround2" -> opcall("Append", tuple(), num(2)),
      "lhs" -> set(tuple(), idexp("workaround1")),
      "rhs" -> set(tuple(), idexp("workaround2"), tuple(num(1), num(2)))),
    expectedStr = "[[1]]")

  check("set of records membership; internally ordered")(
    expr = binop("\\in",
      record(field(id("a"), num(1)), field(id("b"), num(2))),
      set(idexp("r1"), idexp("r2"))),
    vars = List(
      "r1" -> record(field(id("a"), num(1)), field(id("b"), num(2))),
      "r2" -> record(field(id("a"), num(2)), field(id("b"), num(1)))),
    expectedStr = "true")

  check("set of records membership; internally disordered")(
    expr = binop("\\in",
      record(field(id("a"), num(1)), field(id("b"), num(2))),
      set(idexp("r1"), idexp("r2"))),
    vars = List(
      "r1" -> record(field(id("a"), num(2)), field(id("b"), num(1))),
      "r2" -> record(field(id("a"), num(1)), field(id("b"), num(2)))),
    expectedStr = "true")

  check("set of records membership; with strings")(
    expr = binop("\\in",
      record(field(id("a"), num(1)), field(id("b"), str("hi"))),
      set(idexp("r1"), idexp("r2"))),
    vars = List(
      "r1" -> record(field(id("a"), num(2)), field(id("b"), str("nope"))),
      "r2" -> record(field(id("a"), num(1)), field(id("b"), str("hi")))),
    expectedStr = "true")

  check("set of records membership; internally ordered; FALSE")(
    expr = binop("\\in",
      record(field(id("a"), num(1)), field(id("b"), num(2))),
      set(idexp("r1"), idexp("r2"))),
    vars = List(
      "r1" -> record(field(id("a"), num(10)), field(id("b"), num(20))),
      "r2" -> record(field(id("a"), num(20)), field(id("b"), num(10)))),
    expectedStr = "false")

  check("set of records membership; empty set")(
    expr = binop("\\in",
      record(field(id("a"), num(1)), field(id("b"), num(2))),
      set()),
    expectedStr = "false")

  check("quantified universal 2 bounds true")(
    expr = universal(
      bounds(
        qbIds(ids(id("x")), idexp("set1")),
        qbIds(ids(id("y")), idexp("set2"))),
      binop("=",
        binop("%", binop("+", idexp("x"), idexp("y")), num(2)),
        num(1))),
    vars = List(
      "set1" -> set(num(2), num(4), num(6)),
      "set2" -> set(num(1), num(3), num(5))),
    expectedStr = "true")

  check("quantified universal 2 bounds false")(
    expr = universal(
      bounds(
        qbIds(ids(id("x")), idexp("set")),
        qbIds(ids(id("y")), binop("..", num(1), num(3)))),
      binop("=",
        binop("%", binop("+", idexp("x"), idexp("y")), num(2)),
        num(1))),
    vars = List(
      "set" -> set(num(2), num(4), num(6))),
    expectedStr = "false")

  check("tuple concat")(
    expr = binop("\\o", idexp("seq"), tuple(num(10))),
    vars = List(
      "seq" -> tuple(num(1), num(2))),
    expectedStr = "[1 2 10]")

  check("tuple concat with empty")(
    expr = binop("\\o", idexp("seq"), tuple(num(10))),
    vars = List("seq" -> tuple()),
    expectedStr = "[10]")

  check("tuple concat nested")(
    expr = binop("\\o", binop("\\o", tuple(num(1), num(2)), tuple(num(3))), tuple(num(10), num(11))),
    expectedStr = "[1 2 3 10 11]")

  check("tuple subseq last two")(
    expr = opcall("SubSeq", idexp("seq"), num(4), num(5)),
    vars = List(
      "seq" -> tuple(num(1), num(2), num(3), num(4), num(5))),
    expectedStr = "[4 5]")

  check("tuple subseq out of range")(
    expr = opcall("SubSeq", idexp("seq"), num(6), num(5)),
    vars = List(
      "seq" -> tuple(num(1), num(2), num(3), num(4), num(5))),
    expectedStr = "[]")

  check("tuple subseq last element")(
    expr = opcall("SubSeq", idexp("seq"), num(5), num(5)),
    vars = List(
      "seq" -> tuple(num(1), num(2), num(3), num(4), num(5))),
    expectedStr = "[5]")

  check("tuple subseq first element")(
    expr = opcall("SubSeq", idexp("seq"), num(1), num(1)),
    vars = List(
      "seq" -> tuple(num(1), num(2), num(3), num(4), num(5))),
    expectedStr = "[1]")

  check("literal function")(
    expr = function(
      bounds(qbIds(ids(id("x")), set(num(1), num(2), num(3)))),
      idexp("x")),
    expectedStr = "[{1 1} {2 2} {3 3}]")

  check("function call unary")(
    expr = fncall(idexp("fn"), num(2)),
    List("fn" -> function(
      bounds(qbIds(ids(id("x")), set(num(1), num(2), num(3)))),
      binop("+", idexp("x"), num(1)))),
    expectedStr = "3")

  check("function call binary")(
    expr = fncall(idexp("fn"), num(2), num(5)),
    List("fn" -> function(
      bounds(
        qbIds(ids(id("x")), set(num(1), num(2), num(3))),
        qbIds(ids(id("y")), set(num(4), num(5), num(6)))),
      binop("+", idexp("x"), idexp("y")))),
    expectedStr = "7")

  check("set cardinality 2")(
    expr = opcall("Cardinality", set(num(1), num(2))),
    expectedStr = "2")

  check("set cardinality empty")(
    expr = opcall("Cardinality", set()),
    expectedStr = "0")
}
