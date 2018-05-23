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

import pgo.lexer.PGoTLALexerException;
import pgo.lexer.TLALexer;
import pgo.lexer.TLAToken;
import pgo.model.tla.PGoTLABool;
import pgo.model.tla.PGoTLAExpression;
import pgo.util.SourceLocation;

import static pgo.model.tla.Builder.*;

@RunWith(Parameterized.class)
public class TLAExpressionParseTest {

	@Parameters
	public static List<Object[]> data(){
		return Arrays.asList(new Object[][] {
			{"1", num(1) },
			{"TRUE", new PGoTLABool(SourceLocation.unknown(), true) },
			{"FALSE", new PGoTLABool(SourceLocation.unknown(), false) },

			{"[mgr \\in managers |-> \"start\"]",
				function(bounds(qbIds(ids(id("mgr")), idexp("managers"))), str("start")),
			},
			{"a!b", idexp(prefix(idpart("a")), "b") },
			{"a(1,2)!b", idexp(prefix(idpart("a", num(1), num(2))), "b")},
			{"a(1,2)!b(3,4)", opcall(prefix(idpart("a", num(1), num(2))), id("b"), num(3), num(4)) },
			{"a!b!c!d", idexp(prefix(idpart("a"), idpart("b"), idpart("c")), "d") },

			// conjunct/disjunct cases (indent-sensitive)
			{"/\\ a", idexp("a") },
			{"/\\ a\n/\\ b", conjunct(idexp("a"), idexp("b")) },
			{"  /\\ a\n  /\\ b\n/\\ c", conjunct(conjunct(idexp("a"), idexp("b")), idexp("c")) },
			{"  /\\ a\n  /\\ b\n  /\\ c", conjunct(idexp("a"), conjunct(idexp("b"), idexp("c"))) },

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

			// TODO desc
			{"(pc[i] \\notin {\"Li5\", \"Li6\", \"ncs\"})",
					binop("\\notin",
							fncall(idexp("pc"), idexp("i")),
							set(str("Li5"), str("Li6"), str("ncs")))},
		});
	}

	String exprString;
	PGoTLAExpression exprExpected;
	public TLAExpressionParseTest(String exprString, PGoTLAExpression exprExpected) {
		this.exprString = exprString;
		this.exprExpected = exprExpected;
	}

	static Path testFile = Paths.get("TEST");

	@Test
	public void test() throws PGoTLALexerException, TLAParseException {
		TLALexer lexer = new TLALexer(testFile, Arrays.asList(exprString.split("\n")));
		// don't ignore the expression because it's not in a module
		lexer.requireModule(false);

		List<TLAToken> tokens = lexer.readTokens();

		System.out.println(tokens);

		PGoTLAExpression expr = TLAParser.readExpression(tokens.listIterator());

		assertThat(expr, is(exprExpected));
	}

}
