package pgo.parser;

import static org.junit.Assert.*;
import static org.hamcrest.CoreMatchers.*;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pgo.model.tla.TLABool;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAFairness;
import pgo.util.SourceLocation;

import static pgo.model.tla.TLABuilder.*;

@RunWith(Parameterized.class)
public class TLAExpressionParseTest {

	@Parameters
	public static List<Object[]> data(){
		return Arrays.asList(new Object[][] {
				{"1", num(1) },
				{"TRUE", new TLABool(SourceLocation.unknown(), true) },
				{"FALSE", new TLABool(SourceLocation.unknown(), false) },

				{"[mgr \\in managers |-> \"start\"]",
					function(bounds(qbIds(ids(id("mgr")), idexp("managers"))), str("start")),
				},
				{"a!b", idexp(prefix(idpart("a")), "b") },
				{"a(1,2)!b", idexp(prefix(idpart("a", num(1), num(2))), "b")},
				{"a(1,2)!b(3,4)", opcall(prefix(idpart("a", num(1), num(2))), id("b"), num(3), num(4)) },
				{"a!b!c!d", idexp(prefix(idpart("a"), idpart("b"), idpart("c")), "d") },

				// conjunct/disjunct cases (indent-sensitive)
				{"/\\ a", idexp("a") },
				{
					"/\\ a\n"
						+"/\\ b", conjunct(idexp("a"), idexp("b")) },
				{
					"  /\\ a\n"
						+"  /\\ b\n"
						+"/\\ c", conjunct(conjunct(idexp("a"), idexp("b")), idexp("c")) },
				{"  /\\ a\n"
						+"  /\\ b\n"
						+"  /\\ c", conjunct(conjunct(idexp("a"), idexp("b")), idexp("c")) },
				{"  /\\ a\n"
						+"/\\ b\n"
						+"  /\\ c", conjunct(conjunct(idexp("a"), idexp("b")), idexp("c")) },

				// case expressions
				{"CASE x -> 1", caseexp(arms(arm(idexp("x"), num(1))), null) },
				{"CASE x -> 1 [] OTHER -> foo", caseexp(arms(arm(idexp("x"), num(1))), idexp("foo")) },
				{"CASE x -> 1 [] 2 -> 3 [] OTHER -> foo", caseexp(
						arms(
								arm(idexp("x"), num(1)),
								arm(num(2), num(3))),
						idexp("foo"))
				},

				// EXCEPT expressions
				{"[F EXCEPT !.a = 2]", except(idexp("F"), sub(keys(str("a")), num(2))) },
				{"[F EXCEPT ![1] = 2]", except(idexp("F"), sub(keys(num(1)), num(2))) },
				{"[F EXCEPT !.a[1] = 2]", except(idexp("F"), sub(keys(str("a"), num(1)), num(2))) },
				{"[F EXCEPT !.a[1] = 2, !.b = 3]", except(idexp("F"),
						sub(keys(str("a"), num(1)), num(2)),
						sub(keys(str("b")), num(3))
						)
				},
				{"[sum EXCEPT ![self] = msg_'[self]]", except(idexp("sum"),
						sub(keys(idexp("self")), fncall(
								unary("'", idexp("msg_")),
								idexp("self"))))
				},

				// unary operators
				{"a'", unary(prefix(), "'", idexp("a")) },
				{"a'[b]", fncall(unary("'", idexp("a")), idexp("b")) },
				{"a[b]", fncall(idexp("a"), idexp("b")) },

				// precedence tests
				{"DOMAIN \\lnot a", unary("DOMAIN", unary("\\lnot", idexp("a"))) },
				{"\\lnot DOMAIN a", unary("\\lnot", unary("DOMAIN", idexp("a"))) },

				// set construction
				{"0..1", binop("..", num(0), num(1))},
				{"0..procs-1", binop("..", num(0), binop("-", idexp("procs"), num(1)))},

				// TODO desc
				{"x'",
						unary("'", idexp("x"))
				},
				{"x' \\notin y",
						binop("\\notin", unary("'", idexp("x")), idexp("y"))
				},
				{"pc[i] \\notin x",
						binop("\\notin",
								fncall(idexp("pc"), idexp("i")),
								idexp("x"))
				},
				{"pc[i] \\notin {\"Li5\", \"Li6\", \"ncs\"}",
						binop("\\notin",
								fncall(idexp("pc"), idexp("i")),
								set(str("Li5"), str("Li6"), str("ncs")))
				},
				{"(pc[i] \\notin {\"Li5\", \"Li6\", \"ncs\"})",
						binop("\\notin",
								fncall(idexp("pc"), idexp("i")),
								set(str("Li5"), str("Li6"), str("ncs")))},

				// fairness
				{"WF_foo(bar)", fairness(TLAFairness.Type.WEAK, idexp("foo"), idexp("bar"))},

				// indentation
				{"/\\ 1\n" +
						"/\\ 2\n",
						binop("/\\", num(1), num(2))
				},
				{"        /\\ 1\n" +
						"        /\\ 2\n",
						binop("/\\", num(1), num(2))
				},
				{"        /\\ 1 /\\ 2\n" +
						"        /\\ 3\n",
						binop("/\\", binop("/\\", num(1), num(2)), num(3))
				},
				{"        /\\ 1 /\\ []2\n" +
						"        /\\ 3\n",
						binop("/\\", binop("/\\", num(1), unary("[]", num(2))), num(3))
				},
				{"        /\\ 1 /\\ []2 /\\ 3\n",
						binop("/\\", binop("/\\", num(1), unary("[]", num(2))), num(3))
				},
				{"~ /\\ 1\n"
						+"  /\\ 2",
						unary("~", binop("/\\", num(1), num(2)))
				},
				{"[] 2 /\\ 3",
						binop("/\\", unary("[]", num(2)), num(3))
				},
				{"        /\\ Init /\\ 4\n" +
						"        /\\ WF_vars(P(self))",
						binop("/\\",
								binop("/\\",
										idexp("Init"),
										num(4)),
								fairness(TLAFairness.Type.WEAK, idexp("vars"),
										opcall("P", idexp("self"))))
				},
				{"/\\ 1 \\/ 2\n"
						+"/\\ 3",
						binop("/\\", binop("\\/", num(1), num(2)), num(3))
				},
				{"        /\\ Init /\\ 4\n" +
						"        /\\ \\A self \\in 0..procs-1 : WF_vars(P(self))",
						binop("/\\",
								binop("/\\",
										idexp("Init"),
										num(4)),
								universal(
										bounds(
												qbIds(
														ids(id("self")),
														binop("..",
																num(0),
																binop("-", idexp("procs"), num(1))))
										),
										fairness(TLAFairness.Type.WEAK, idexp("vars"),
												opcall("P", idexp("self")))))
				},

				// tuple
				{"<<24, v_init, \"have gcd\", v>>",
						tuple(num(24), idexp("v_init"), str("have gcd"), idexp("v"))
				},

				// postfix / performance
				{"msg'[1]",
						fncall(unary("'", idexp("msg")), num(1))
				},
				{"Append(output, msg'[1])",
						opcall("Append", idexp("output"), fncall(unary("'", idexp("msg")), num(1)))
				},
				/*{"Append(network[(N+1)], <<self, (<<a_init[self],b_init[self]>>)>>)",
						opcall("Append", )
				},*/

				// a string with spaces in it
				{"\"have gcd\"",
						str("have gcd")
				},

				{"pc[self] = \"c1\"",
						binop("=", fncall(idexp("pc"), idexp("self")), str("c1"))
				},

				{"            /\\ pc[self] = \"c1\"\n" +
						"            /\\ (restaurant_stage[self] = \"commit\") \\/\n" +
						"               (restaurant_stage[self] = \"abort\")\n" +
						"            /\\ IF restaurant_stage[self] = \"commit\"\n" +
						"                  THEN /\\ restaurant_stage' = [restaurant_stage EXCEPT ![self] = \"committed\"]\n" +
						"                  ELSE /\\ restaurant_stage' = [restaurant_stage EXCEPT ![self] = \"aborted\"]\n" +
						"            /\\ pc' = [pc EXCEPT ![self] = \"Done\"]\n" +
						"            /\\ UNCHANGED << managers, rstMgrs, aborted >>",
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
										tuple(idexp("managers"), idexp("rstMgrs"), idexp("aborted"))))
				},

				{
					"(2)",
						num(2)
				},
				{
					"(restaurant_stage[self] = \"commit\")",
						binop("=", fncall(idexp("restaurant_stage"), idexp("self")), str("commit"))
				},

				{"\\A x \\in set,y \\in (1)..(3) : (((x)+(y))%(2))=(1)",
						universal(
								bounds(
										qbIds(ids(id("x")), idexp("set")),
										qbIds(ids(id("y")), binop("..", num(1), num(3)))),
								binop("=",
										binop("%",
												binop("+",
														idexp("x"),
														idexp("y")),
												num(2)),
										num(1)))
				},

				{"\\A i \\in Proc :\n                     (pc[i] = \"Li0\") ~> (\\E j \\in Proc : pc[j] = \"cs\")",
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
														str("cs")))))
				},
		});
	}

	String exprString;
	TLAExpression exprExpected;
	public TLAExpressionParseTest(String exprString, TLAExpression exprExpected) {
		this.exprString = exprString;
		this.exprExpected = exprExpected;
	}

	static Path testFile = Paths.get("TEST");

	@Test
	public void test() throws ParseFailureException {
		LexicalContext ctx = new LexicalContext(testFile, String.join(System.lineSeparator(), exprString.split("\n")));

		System.out.println(exprString);

		TLAExpression expr = TLAParser.readExpression(ctx);

		assertThat(expr, is(exprExpected));
	}

}
