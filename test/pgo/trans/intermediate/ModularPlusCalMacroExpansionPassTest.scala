package pgo.trans.intermediate

import org.scalactic.source.Position

import java.util.Collections
import org.scalatest.funsuite.AnyFunSuite
import pgo.TestingUtils
import pgo.errors.TopLevelIssueContext
import pgo.model.mpcal.ModularPlusCalBlock
import pgo.model.pcal.PlusCalAlgorithm
import pgo.trans.passes.expansion.ModularPlusCalMacroExpansionPass
import pgo.model.pcal.PlusCalBuilder._
import pgo.model.tla.TLABuilder._

import scala.jdk.CollectionConverters._


class ModularPlusCalMacroExpansionPassTest extends AnyFunSuite {
  def check(tag: String)(pair: (PlusCalAlgorithm,PlusCalAlgorithm))(implicit pos: Position): Unit =
    test(tag) {
      val (beforePCal, expectedPCal) = pair
      val before = ModularPlusCalBlock.from(beforePCal)
      val (_,reparsedBefore) = TestingUtils.reparseMPCal(before)
      val expected = ModularPlusCalBlock.from(expectedPCal)
      val ctx = new TopLevelIssueContext
      val actual = ModularPlusCalMacroExpansionPass.perform(ctx, reparsedBefore)
      assert(actual == expected)
    }

  check("simple") {
    algorithm(
      "Test",
      List(pcalVarDecl("a", false, false, str("a"))).asJava,
      Collections.singletonList(`macro`(
        "mymacro", Collections.singletonList("a"),
        `with`(List(pcalVarDecl("b", false, false, str("b"))).asJava,
          printS(idexp("a")),
          printS(idexp("b"))))),
      Collections.emptyList,
      Collections.emptyList,
      labeled(
        label("foo"),
        printS(idexp("a")),
        macroCall("mymacro", binop("+", num(2), num(2))))
    ) -> algorithm(
      "Test",
      List(pcalVarDecl("a", false, false, str("a"))).asJava,
      Collections.emptyList,
      Collections.emptyList,
      Collections.emptyList,
      labeled(
        label("foo"),
        printS(idexp("a")),
        `with`(List(pcalVarDecl("b", false, false, str("b"))).asJava,
          printS(binop("+", num(2), num(2))),
          printS(idexp("b")))))
  }
}