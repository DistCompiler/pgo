package pgo.parser

import org.scalatest.funsuite.AnyFunSuite
import pgo.model.tla._
import TLABuilder._
import org.scalactic.source.Position
import pgo.TestingUtils

import scala.jdk.CollectionConverters._

class TLAUnitParseTest extends AnyFunSuite with TLAParser with ParsingUtils {
  def check(tag: String)(pair: (String, TLAUnit))(implicit pos: Position): Unit =
    test(tag) {
      val (input, expected) = pair
      val backingFile = ParserTestingUtils.ensureBackingFile(input)
      withClue(s"input:\n$input") {
        val defns = TLABuiltinModules.Intrinsics.members ++
          TLABuiltinModules.Integers.members ++ TLABuiltinModules.Sequences.members
        implicit val ctx = defns.foldLeft(TLAParserContext())(_.withDefinition(_))
        val actual = checkResult {
          (wsChk ~> tlaUnit <~ wsChk) (buildReader(backingFile, input))
        }
        withClue("\n" + TestingUtils.stringDiff(expected = expected.toString, actual = actual.toString).mkString("\n")) {
          assert(expected == actual)
        }
      }
    }

  check("queens IsSolution") {
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

  check("queens Solutions") {
    """Solutions == LET N == 42 IsSolution(x) == FALSE IN { queens \in [1..N -> 1..N] : IsSolution(queens) }""" ->
      opdef(false, id("Solutions"), opdecls(),
        let(
          List[TLAUnit](
            opdef(false, id("N"), opdecls(), num(42)),
            opdef(false, id("IsSolution"), opdecls(opdecl(id("x"))), bool(false))).asJava,
          setRefinement("queens",
            functionSet(binop("..", num(1), idexp("N")), binop("..", num(1), idexp("N"))),
            opcall("IsSolution", idexp("queens")))))
  }

  check("dashed prefix") {
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

  check("deadlockFreedom") {
    """DeadlockFreedom ==
      |    \E pc, Proc :
      |    \A i \in Proc :
      |      (pc[i] \notin {"Li5", "Li6", "ncs"}) ~> (\E j \in Proc : pc[j] = "cs")
      |""".stripMargin ->
      opdef(false, id("DeadlockFreedom"), opdecls(),
        uqExistential(List(id("pc"), id("Proc")).asJava,
          universal(bounds(qbIds(ids(id("i")), idexp("Proc"))),
            binop("~>",
              binop("\\notin",
                fncall(idexp("pc"), idexp("i")),
                set(str("Li5"), str("Li6"), str("ncs"))),
              existential(bounds(qbIds(ids(id("j")), idexp("Proc"))),
                binop("=",
                  fncall(idexp("pc"), idexp("j")),
                  str("cs")))))))
  }

  check("Termination") {
    """Termination == \E pc : <>(pc = "Done")""".stripMargin ->
      opdef(false, id("Termination"), opdecls(),
        uqExistential(List(id("pc")).asJava,
          unary("<>", binop("=", idexp("pc"), str("Done")))))
  }

  check("Spec") {
    """Spec(self, Init, P(_), procs, vars) ==
      |        /\ Init /\ []4
      |        /\ \A self \in 0..procs-1 : WF_vars(P(self))""".stripMargin ->
      opdef(false, id("Spec"),
        opdecls(
          opdecl(id("self")),
          opdecl(id("Init")),
          opdeclNamed(id("P"), 1),
          opdecl(id("procs")),
          opdecl(id("vars"))),
        binop("/\\",
          binop("/\\",
            idexp("Init"),
            unary("[]",
              num(4))),
          universal(
            bounds(
              qbIds(
                ids(id("self")),
                binop("..",
                  num(0),
                  binop("-", idexp("procs"), num(1))))),
            fairness(TLAFairness.Type.WEAK, idexp("vars"),
              opcall("P", idexp("self"))))))
  }

  check("large conjunct") {
    """c1(self) == \E pc, managers, rstMgrs, aborted, restaurant_stage :
      |            /\ pc[self] = "c1"
      |            /\ (restaurant_stage[self] = "commit") \/
      |               (restaurant_stage[self] = "abort")
      |            /\ IF restaurant_stage[self] = "commit"
      |                  THEN /\ restaurant_stage' = [restaurant_stage EXCEPT ![self] = "committed"]
      |                  ELSE /\ restaurant_stage' = [restaurant_stage EXCEPT ![self] = "aborted"]
      |            /\ pc' = [pc EXCEPT ![self] = "Done"]
      |            /\ UNCHANGED << managers, rstMgrs, aborted >>""".stripMargin ->
      opdef(false, id("c1"), opdecls(opdecl(id("self"))),
        uqExistential(List(id("pc"), id("managers"), id("rstMgrs"), id("aborted"), id("restaurant_stage")).asJava,
          binop("/\\",
            binop("/\\",
              binop("/\\",
                binop("/\\",
                  binop("=", fncall(idexp("pc"), idexp("self")), str("c1")),
                  binop("\\/",
                    binop("=",
                      fncall(idexp("restaurant_stage"), idexp("self")),
                      str("commit")),
                    binop("=",
                      fncall(idexp("restaurant_stage"), idexp("self")),
                      str("abort")))),
                ifexp(
                  binop("=",
                    fncall(idexp("restaurant_stage"), idexp("self")),
                    str("commit")),
                  binop("=",
                    unary("'", idexp("restaurant_stage")),
                    except(
                      idexp("restaurant_stage"),
                      sub(keys(idexp("self")), str("committed")))),
                  binop("=",
                    unary("'", idexp("restaurant_stage")),
                    except(
                      idexp("restaurant_stage"),
                      sub(keys(idexp("self")), str("aborted")))))),
              binop("=",
                unary("'", idexp("pc")),
                except(
                  idexp("pc"),
                  sub(keys(idexp("self")), str("Done"))))),
            unary("UNCHANGED",
              tuple(idexp("managers"), idexp("rstMgrs"), idexp("aborted"))))))
  }

  check("embedded comment") {
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

  check("DeadlockFree") {
    """DeadlockFree == \E pc, Proc : \A i \in Proc :
      |                     (pc[i] = "Li0") ~> (\E j \in Proc : pc[j] = "cs")""".stripMargin ->
      opdef(false, id("DeadlockFree"), opdecls(),
        uqExistential(List(id("pc"), id("Proc")).asJava,
          universal(
            bounds(qbIds(ids(id("i")), idexp("Proc"))),
            binop("~>",
              binop("=",
                fncall(idexp("pc"), idexp("i")),
                str("Li0")),
              existential(
                bounds(qbIds(ids(id("j")), idexp("Proc"))),
                binop("=",
                  fncall(idexp("pc"), idexp("j")),
                  str("cs")))))))
  }
}
