package pgo.parser

import org.scalatest.funsuite.AnyFunSuite
import pgo.TestingUtils
import pgo.model.mpcal.ModularPlusCalBlock
import pgo.model.mpcal.ModularPlusCalBuilder._
import pgo.model.pcal.PlusCalBuilder._
import pgo.model.pcal.{PlusCalFairness, PlusCalStatement}
import pgo.model.tla.TLABuilder._

import scala.jdk.CollectionConverters._

class ModularPlusCalParserTest extends AnyFunSuite {
  def check(tag: String)(pair: (String,ModularPlusCalBlock)): Unit =
    test(tag) {
      val(specStr,expectedBlock) = pair
      val (_, _, actualBlock) = TestingUtils.parseMPCalFromString(specStr)
      assert(actualBlock == expectedBlock)
    }

  check("single-process with procedure and macro") {
    """---- MODULE Test ----
      |(* --mpcal Test {
      |     macro M(a) {
      |       print a;
      |     }
      |     procedure P(b) {
      |       print b;
      |     }
      |     variables global1 = 1, global2 = 2;
      |     {
      |       l1: print <<global1, global2>>;
      |     }
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====""".stripMargin -> mpcal(
      "Test",
      Nil.asJava,
      List(
        `macro`("M",
          List("a").asJava,
          printS(idexp("a")))).asJava,
      List(
        procedure("P",
          List(pcalVarDecl("b", false, false, PLUSCAL_DEFAULT_INIT_VALUE)).asJava,
          Nil.asJava,
          printS(idexp("b")))).asJava,
      Nil.asJava,
      Nil.asJava,
      List(
        pcalVarDecl("global1", false, false, num(1)),
        pcalVarDecl("global2", false, false, num(2))).asJava,
      Nil.asJava,
      List[PlusCalStatement](
        labeled(label("l1"),
          printS(tuple(idexp("global1"), idexp("global2"))))).asJava)
  }

  check("multi-process with procedure and macro") {
    """---- MODULE Test ----
      |EXTENDS Integers
      |(* --mpcal Test {
      |     macro M(a) {
      |       print a;
      |     }
      |     procedure P(b) {
      |       print b;
      |     }
      |     variables global1 = 1, global2 = 2;
      |     process (P \in 1..3) {
      |       l1: print <<global1, global2>>;
      |     }
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin -> mpcal(
      "Test",
      Nil.asJava,
      List(
        `macro`("M",
          List("a").asJava,
          printS(idexp("a")))).asJava,
      List(
        procedure("P",
          List(pcalVarDecl("b", false, false, PLUSCAL_DEFAULT_INIT_VALUE)).asJava,
          Nil.asJava,
          printS(idexp("b")))).asJava,
      Nil.asJava,
      Nil.asJava,
      List(
        pcalVarDecl("global1", false, false, num(1)),
        pcalVarDecl("global2", false, false, num(2))).asJava,
      Nil.asJava,
      process(
        pcalVarDecl("P", false, true, binop("..", num(1), num(3))),
        PlusCalFairness.UNFAIR,
        Nil.asJava,
        labeled(label("l1"),
          printS(tuple(idexp("global1"), idexp("global2"))))))
  }
}
