package pgo.parser

import org.scalatest.funsuite.AnyFunSuite
import pgo.model.tla._
import TLABuilder._

import scala.jdk.CollectionConverters._

class TLAUnitParseTest extends AnyFunSuite with TLAParserTestUtils with TLAParser {
  def testUnitParse(tag: String)(pair: (String, TLAUnit)): Unit = {
    val (input, expected) = pair
    test(tag) {
      implicit val ctx = TLAParserContext()
      testParserOutput(input, wsChk ~> tlaUnit <~ wsChk, expected)
    }
  }

  testUnitParse("queens IsSolution") {
    """---- MODULE Test ----
      |EXTENDS Sequences, Integers
      |
      |Attacks(queens, i, j) == "stub"
      |IsSolution(queens) ==
      |  \A i \in 1 .. Len(queens)-1 : \A j \in i+1 .. Len(queens) :
      |       ~ Attacks(queens,i,j)
      |====
      |""".stripMargin -> module(
      "Test",
      List(id("Sequences"), id("Integers")).asJava,
      List[TLAUnit](
        opdef(false, id("Attacks"), List(opdecl(id("queens")), opdecl(id("i")), opdecl(id("j"))).asJava,
          str("stub")),
        opdef(false, id("IsSolution"), List(opdecl(id("queens"))).asJava,
          universal(bounds(qbIds(ids(id("i")), binop("..", num(1), binop("-", opcall("Len", idexp("queens")), num(1))))),
            universal(bounds(qbIds(ids(id("j")), binop("..", binop("+", idexp("i"), num(1)), opcall("Len", idexp("queens"))))),
              unary("~", opcall("Attacks", idexp("queens"), idexp("i"), idexp("j"))))))).asJava)
  }

  testUnitParse("dashed prefix") {
    """---- MODULE Test ----
      |CONSTANTS pc, Proc
      |
      |-----------------------------------------------------------------------------
      |MutualExclusion == \A i, j \in Proc :
      |                     (i # j) => ~ /\ pc[i] = "cs"
      |                                  /\ pc[j] = "cs"
      |====
      |""".stripMargin -> module(
      "Test",
      Nil.asJava,
      List[TLAUnit](
        constants(opdecl(id("pc")), opdecl(id("Proc"))),
        opdef(false, id("MutualExclusion"), opdecls(),
          universal(bounds(qbIds(ids(id("i"), id("j")), idexp("Proc"))),
            binop("=>", binop("#", idexp("i"), idexp("j")),
              unary("~", conjunct(
                binop("=",
                  fncall(idexp("pc"), idexp("i")),
                  str("cs")),
                binop("=",
                  fncall(idexp("pc"), idexp("j")),
                  str("cs")))))))).asJava)
  }

  testUnitParse("embedded comment") {
    """----- MODULE Test ----
      |EXTENDS Sequences, Integers
      |(* --algorithm Test {
      |    variables a = 2; \n" +
      |          b = 2; \n" +
      |          c = 3; \n" +
      |    {    \n" +
      |        print (a)*((b)+(c))\n" +
      |    }    \n" +
      |}
      |*)
      |
      |B == FALSE
      |----
      |LOCAL C == TRUE
      |====""".stripMargin -> module(
      "Test",
      List(id("Sequences"), id("Integers")).asJava,
      List[TLAUnit](
        opdef(false, id("B"), Nil.asJava, bool(false)),
        opdef(true, id("C"), Nil.asJava, bool(true))).asJava)
  }
}
