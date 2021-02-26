package pgo.parser

import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite

import java.util
import java.util.Collections
import pgo.model.tla.{TLABool, TLABuiltinModules, TLAExpression, TLAFairness}
import pgo.util.SourceLocation
import pgo.model.tla.TLABuilder._

class TLAExpressionParseTest extends AnyFunSuite {
  def check(tag: String)(pair: (String,TLAExpression))(implicit pos: Position): Unit =
    test(tag) {
      val (str, expected) = pair
      withClue(str) {
        val testFile = ParserTestingUtils.ensureBackingFile(str)
        val expr = TLAParser.readExpression(
          testFile,
          str,
          definitions = TLABuiltinModules.Integers.members ++
            TLABuiltinModules.Sequences.members ++
            TLABuiltinModules.Bags.members) // needed for (+)
        assert(expr == expected)
      }
    }
  // TODO: re-introduce in a way that makes sense given scoping
  //				{"a!b", idexp(prefix(idpart("a")), "b") },
  //				{"a(1,2)!b", idexp(prefix(idpart("a", num(1), num(2))), "b")},
  //				{"a(1,2)!b(3,4)", opcall(prefix(idpart("a", num(1), num(2))), id("b"), num(3), num(4)) },
  //				{"a!b!c!d", idexp(prefix(idpart("a"), idpart("b"), idpart("c")), "d") },

  // simple exprs
  check("1") {
    "1" -> num(1)
  }
  check("-1") {
    "-1" -> unary("-_", num(1))
  }
  check("(2)") {
    "(2)" -> num(2)
  }
  check("TRUE") {
    "TRUE" -> new TLABool(SourceLocation.unknown, true)
  }
  check("FALSE") {
    "FALSE" -> new TLABool(SourceLocation.unknown, false)
  }
  check("some string") {
    "\"some string\"" -> str("some string")
  }
  check("function") {
    """[mgr \in "managers" |-> "start"]""" -> function(
      bounds(qbIds(ids(id("mgr")), str("managers"))),
      str("start"))
  }
  check("set refinement ambiguity") {
    """{ a \in "B" : a \in a }""" -> setRefinement(
      "a",
      str("B"),
      binop("\\in", idexp("a"), idexp("a")))
  }
  check("record constructor") {
    """[src |-> "clientId", dst |-> "serverId"]""" -> record(
      field(id("src"), str("clientId")),
      field(id("dst"), str("serverId")))
  }
  check("empty tuple") {
    "<< >>" -> tuple()
  }
  check("empty set") {
    "{ }" -> set()
  }
  check("set containing empty tuple") {
    "{ << >> }" -> set(tuple())
  }
  check("tuple 3") {
    "<<24, \"v_init\", \"have gcd\", \"v\">>" -> tuple(
      num(24), str("v_init"), str("have gcd"), str("v"))
  }

  // unary operators
  check("prime operator") {
    """"a"'""" -> unary(prefix(), "'", str("a"))
  }
  check("function call on primed expr") {
    """"a"'["b"]""" -> fncall(unary("'", str("a")), str("b"))
  }
  check("function call plain") {
    """"a"["b"]""" -> fncall(str("a"), str("b"))
  }
  check("prefixes: DOMAIN then lnot") {
    """DOMAIN \lnot "a"""" -> unary("DOMAIN", unary("\\lnot", str("a")))
  }
  check("prefixes: lnot then DOMAIN") {
    """\lnot DOMAIN "a"""" -> unary("\\lnot", unary("DOMAIN", str("a")))
  }

  // infix operators
  check("assignment of set of empty tuple") {
    "\"todo\" = { << >> }" -> binop("=", str("todo"), set(tuple()))
  }
  check("number ..") {
    """0..1""" -> binop("..", num(0), num(1))
  }
  check("compound ..") {
    """0.."procs"-1""" -> binop("..", num(0), binop("-", str("procs"), num(1)))
  }

  check("prime with infix") {
    """"x"' \notin "y"""" -> binop("\\notin", unary("'", str("x")), str("y"))
  }
  check("function call with infix") {
    """"pc"["i"] \notin "x"""" -> binop(
      "\\notin",
      fncall(str("pc"), str("i")),
      str("x"))
  }
  check("function call with bigger infix") {
    """"pc"["i"] \notin {"Li5", "Li6", "ncs"}""" -> binop(
      "\\notin",
      fncall(str("pc"), str("i")),
      set(str("Li5"), str("Li6"), str("ncs")))
  }
  check("function call with assignment") {
    """"pc"["self"] = "c1"""" -> binop("=", fncall(str("pc"), str("self")), str("c1"))
  }

  // dotted
  check("single dot expr") {
    """"a".b""" -> dot(str("a"), "b")
  }
  check("chained dot expr") {
    """"a".b.c""" -> dot(dot(str("a"), "b"), "c")
  }
  check("dot with function call") {
    """"a"[1].b""" -> dot(fncall(str("a"), num(1)), "b")
  }
  check("dot with grouped function call") {
    """("a"[1]).b""" -> dot(fncall(str("a"), num(1)), "b")
  }
  check("dot with prime") {
    """"a"'.b""" -> dot(unary("'", str("a")), "b")
  }
  check("nested primed dots") {
    """"a"'.b'.c""" -> dot(unary("'", dot(unary("'", str("a")), "b")), "c")
  }
  check("dot with infix") {
    """"a" (+) "b".d""" -> binop("(+)", str("a"), dot(str("b"), "d"))
  }
  check("dot with grouped infix") {
    """("a" \cup "b").c""" -> dot(binop("\\cup", str("a"), str("b")), "c")
  }
  check("dot with record construction") {
    """[src |-> "clientId", dst |-> "serverId"].src""" -> dot(
      record(field(id("src"), str("clientId")), field(id("dst"), str("serverId"))),
      "src")
  }

  // conjuncts
  check("unary conjunct") {
    """/\ 1""" -> num(1)
  }
  check("conjunct 2 aligned") {
    """/\ 1
      |/\ 2""".stripMargin -> conjunct(num(1), num(2))
  }
  check("conjunct 2 trailing dedent") {
    """  /\ 1
      |  /\ 2
      |/\ 3""".stripMargin -> conjunct(conjunct(num(1), num(2)), num(3))
  }
  check("conjunct 3 aligned") {
    """  /\ 1
      |  /\ 2
      |  /\ 3""".stripMargin -> conjunct(conjunct(num(1), num(2)), num(3))
  }
  check("infix conjunct due to misalignment") {
    """  /\ 1
      |/\ 2
      |  /\ 3""".stripMargin -> conjunct(conjunct(num(1), num(2)), num(3))
  }
  check("conjunct 2 with trailing new line") {
    """/\ 1
      |/\ 2
      |""".stripMargin -> binop("/\\", num(1), num(2))
  }
  check("indented conjunct 2 with trailing new line") {
    """        /\ 1
      |        /\ 2
      |""".stripMargin -> binop("/\\", num(1), num(2))
  }
  check("conjunct 2 with nested conjunct 1") {
    """        /\ 1 /\ 2
      |        /\ 3
      |""".stripMargin -> binop("/\\", binop("/\\", num(1), num(2)), num(3))
  }
  check("conjunct 2 with nested conjunct 1 + prefix op") {
    """        /\ 1 /\ []2
      |        /\ 3
      |""".stripMargin -> binop(
      "/\\",
      binop("/\\", num(1), unary("[]", num(2))),
      num(3))
  }
  check("triple nested conjunct 1") {
    """        /\ 1 /\ []2 /\ 3
      |""".stripMargin -> binop(
      "/\\",
      binop("/\\", num(1), unary("[]", num(2))),
      num(3))
  }
  check("conjunct 2 with prefix op") {
    """~ /\ 1
      |  /\ 2""".stripMargin -> unary("~", binop("/\\", num(1), num(2)))
  }
  check("infix conjunct with prefix op") {
    """[] 2 /\ 3""" -> binop("/\\", unary("[]", num(2)), num(3))
  }
  check("conjunct 2 with nested WF_") {
    """        /\ "Init" /\ 4
      |        /\ WF_"vars"("P(self)")""".stripMargin -> binop(
      "/\\",
      binop("/\\", str("Init"), num(4)),
      fairness(TLAFairness.Type.WEAK, str("vars"), str("P(self)")))
  }
  check("conjunct 2 with nested disjunct") {
    """/\ 1 \/ 2
      |/\ 3""".stripMargin -> binop("/\\", binop("\\/", num(1), num(2)), num(3))
  }
  check("conjunct 2 with nested conjunct 1 + universal + WF_") {
    """        /\ "Init" /\ 4
      |        /\ \A self \in 0.."procs"-1 : WF_self("P"[self])""".stripMargin -> binop(
      "/\\",
      binop("/\\", str("Init"), num(4)),
      universal(
        bounds(qbIds(
          ids(id("self")),
          binop("..", num(0), binop("-", str("procs"), num(1))))),
        fairness(TLAFairness.Type.WEAK, idexp("self"), fncall(str("P"), idexp("self")))))
  }

  // case exprs
  check("case one branch") {
    """CASE 0 -> 1""" -> caseexp(arms(arm(num(0), num(1))), null)
  }
  check("case one branch with other") {
    """CASE 0 -> 1
      |[] OTHER -> "foo"""".stripMargin -> caseexp(arms(arm(num(0), num(1))), str("foo"))
  }
  check("case 2 branches with other") {
    """CASE 0 -> 1
      |[] 2 -> 3
      |[] OTHER -> "foo"""".stripMargin -> caseexp(
      arms(
        arm(num(0), num(1)),
        arm(num(2), num(3))),
      str("foo"))
  }

  // existentials and universals
  check("universal over empty set") {
    """\A i \in {} : i = 1""" -> universal(
      Collections.singletonList(qbIds(Collections.singletonList(id("i")), set())),
      binop("=", idexp("i"), num(1)))
  }
  check("existential over empty set") {
    """\E i \in {} : i = 1""" -> existential(
      Collections.singletonList(qbIds(Collections.singletonList(id("i")), set())),
      binop("=", idexp("i"), num(1)))
  }
  check("forall over multiple bounds") {
    """\A x \in "set",y \in (1)..(3) : (((x)+(y))%(2))=(1)""" -> universal(
      bounds(
        qbIds(ids(id("x")), str("set")),
        qbIds(ids(id("y")), binop("..", num(1), num(3)))),
      binop("=", binop("%", binop("+", idexp("x"), idexp("y")), num(2)), num(1)))
  }
  check("unqualified existential") {
    """\E restaurant_stage, self : (restaurant_stage[self] = "commit")""" -> uqExistential(
      util.Arrays.asList(id("restaurant_stage"), id("self")),
      binop("=", fncall(idexp("restaurant_stage"), idexp("self")), str("commit")))
  }

  // bindings + WF_
  check("WF_ with arity 0 identifier in vars position") {
    """\E foo, bar :
      |WF_foo(bar)""".stripMargin -> uqExistential(
      util.Arrays.asList(id("foo"), id("bar")),
      fairness(TLAFairness.Type.WEAK, idexp("foo"), idexp("bar")))
  }
  check("WF_ with parameterised operator in vars position") {
    """LET foo(x) == x
      |    bar == 0
      |IN  WF_foo(bar)(bar)""".stripMargin -> let(
      util.Arrays.asList(
        opdef(false, id("foo"), Collections.singletonList(opdecl(id("x"))), idexp("x")),
        opdef(false, id("bar"), Collections.emptyList, num(0))),
      fairness(TLAFairness.Type.WEAK, opcall("foo", idexp("bar")), idexp("bar")))
  }
  check("operator call arity 2") {
    """LET Append(x,y) == 0
      |IN Append("output", "msg"'[1])""".stripMargin -> let(
      util.Arrays.asList(
        opdef(false, id("Append"), util.Arrays.asList(opdecl(id("x")), opdecl(id("y"))), num(0))),
      opcall("Append", str("output"), fncall(unary("'", str("msg")), num(1))))
  }

  // EXCEPT
  check("EXCEPT one id") {
    """["F" EXCEPT !.a = 2]""" -> except(str("F"), sub(keys(str("a")), num(2)))
  }
  check("EXCEPT one idx") {
    """["F" EXCEPT ![1] = 2]""" -> except(str("F"), sub(keys(num(1)), num(2)))
  }
  check("EXCEPT one id with idx") {
    """["F" EXCEPT !.a[1] = 2]""" -> except(str("F"), sub(keys(str("a"), num(1)), num(2)))
  }
  check("EXCEPT two: id with idx, and id") {
    """["F" EXCEPT !.a[1] = 2, !.b = 3]""" -> except(
      str("F"),
      sub(keys(str("a"), num(1)), num(2)),
      sub(keys(str("b")), num(3)))
  }
  check("EXCEPT one string idx") {
    """["sum" EXCEPT !["self"] = "msg_"'["self"]]""" -> except(
      str("sum"),
      sub(keys(str("self")), fncall(unary("'", str("msg_")), str("self"))))
  }

  // big
  check("big compound expression") {
    """\E pc, self, restaurant_stage, managers, rstMgrs, aborted :
      |            /\ pc[self] = "c1"
      |            /\ (restaurant_stage[self] = "commit") \/
      |               (restaurant_stage[self] = "abort")
      |            /\ IF restaurant_stage[self] = "commit"
      |                  THEN /\ restaurant_stage' = [restaurant_stage EXCEPT ![self] = "committed"]
      |                  ELSE /\ restaurant_stage' = [restaurant_stage EXCEPT ![self] = "aborted"]
      |            /\ pc' = [pc EXCEPT ![self] = "Done"]
      |            /\ UNCHANGED << managers, rstMgrs, aborted >>""".stripMargin -> uqExistential(
      util.Arrays.asList(
        id("pc"), id("self"), id("restaurant_stage"), id("managers"),
        id("rstMgrs"), id("aborted")),
      binop(
        "/\\",
        binop(
          "/\\",
          binop(
            "/\\",
            binop(
              "/\\",
              binop("=", fncall(idexp("pc"), idexp("self")), str("c1")),
              binop(
                "\\/",
                binop("=", fncall(idexp("restaurant_stage"), idexp("self")), str("commit")),
                binop("=", fncall(idexp("restaurant_stage"), idexp("self")), str("abort")))),
            ifexp(
              binop("=", fncall(idexp("restaurant_stage"), idexp("self")), str("commit")),
              binop(
                "=",
                unary("'", idexp("restaurant_stage")),
                except(idexp("restaurant_stage"), sub(keys(idexp("self")), str("committed")))),
              binop(
                "=",
                unary("'", idexp("restaurant_stage")),
                except(idexp("restaurant_stage"), sub(keys(idexp("self")), str("aborted")))))),
          binop("=", unary("'", idexp("pc")), except(idexp("pc"), sub(keys(idexp("self")), str("Done"))))),
        unary("UNCHANGED", tuple(idexp("managers"), idexp("rstMgrs"), idexp("aborted")))))
  }
  check("big nested universal") {
    """\A i \in "Proc" :
      |                     ("pc"[i] = "Li0") ~> (\E j \in "Proc" : "pc"[j] = "cs")""".stripMargin -> universal(
      bounds(qbIds(ids(id("i")), str("Proc"))),
      binop(
        "~>",
        binop("=", fncall(str("pc"), idexp("i")), str("Li0")),
        existential(
          bounds(qbIds(ids(id("j")), str("Proc"))),
          binop("=", fncall(str("pc"), idexp("j")), str("cs")))))
  }
}