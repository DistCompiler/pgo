package pgo.parser;

import static org.junit.Assert.*;
import static org.hamcrest.CoreMatchers.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pcal.TLAToken;
import pgo.lexer.PGoTLALexerException;
import pgo.lexer.TLALexer;
import pgo.model.tla.PGoTLABool;
import pgo.model.tla.PGoTLACase;
import pgo.model.tla.PGoTLACaseArm;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLAFunction;
import pgo.model.tla.PGoTLAFunctionSubstitution;
import pgo.model.tla.PGoTLAFunctionSubstitutionPair;
import pgo.model.tla.PGoTLAGeneralIdentifierPart;
import pgo.model.tla.PGoTLANumber;
import pgo.model.tla.PGoTLAOperatorCall;
import pgo.model.tla.PGoTLAQuantifierBound;
import pgo.model.tla.PGoTLAString;
import pgo.model.tla.PGoTLASubstitutionKey;
import pgo.model.tla.PGoTLASubstitutionKeyIndices;
import pgo.model.tla.PGoTLASubstitutionKeyName;
import pgo.model.tla.PGoTLAVariable;

@RunWith(Parameterized.class)
public class TLAExpressionParseTest {

	@Parameters
	public static List<Object[]> data(){
		return Arrays.asList(new Object[][] {
			{"[mgr \\in managers |-> \"start\"]", new PGoTLAFunction(
					Arrays.asList(new PGoTLAQuantifierBound[] {
							new PGoTLAQuantifierBound(
									Arrays.asList(new String[] {"mgr",}),
									new PGoTLAVariable(
											"managers",
											new ArrayList<>(),
											1)),
					}),
					new PGoTLAString("start", 1),
					1),
			},
			{"a!b", new PGoTLAVariable("b",
					Arrays.asList(new PGoTLAGeneralIdentifierPart[] {
							new PGoTLAGeneralIdentifierPart("a", new ArrayList<>()),
					}),
					1),
			},
			{"a(1,2)!b", new PGoTLAVariable("b",
					Arrays.asList(new PGoTLAGeneralIdentifierPart[] {
							new PGoTLAGeneralIdentifierPart("a",
									Arrays.asList(new PGoTLAExpression[] {
											new PGoTLANumber("1", 1),
											new PGoTLANumber("2", 1),
									})),
					}),
					1),
			},
			{"a(1,2)!b(3,4)", new PGoTLAOperatorCall(-1, "b",
					Arrays.asList(new PGoTLAGeneralIdentifierPart[] {
							new PGoTLAGeneralIdentifierPart("a",
									Arrays.asList(new PGoTLAExpression[] {
											new PGoTLANumber("1", 1),
											new PGoTLANumber("2", 1),
									})),
					}),
					Arrays.asList(new PGoTLAExpression[] {
							new PGoTLANumber("3", 1),
							new PGoTLANumber("4", 1),
					})),
			},
			{"CASE x -> 1", new PGoTLACase(
					Arrays.asList(new PGoTLACaseArm[] {
						new PGoTLACaseArm(
								new PGoTLAVariable("x", new ArrayList<>(), 1),
								new PGoTLANumber("1", 1)),	
					}),
					null,
					1),
			},
			{"CASE x -> 1 [] OTHER -> foo", new PGoTLACase(
					Arrays.asList(new PGoTLACaseArm[] {
						new PGoTLACaseArm(
								new PGoTLAVariable("x", new ArrayList<>(), 1),
								new PGoTLANumber("1", 1)),	
					}),
					new PGoTLAVariable("foo", new ArrayList<>(), 1),
					1),
			},
			{"CASE x -> 1 [] 2 -> 3 [] OTHER -> foo", new PGoTLACase(
					Arrays.asList(new PGoTLACaseArm[] {
						new PGoTLACaseArm(
								new PGoTLAVariable("x", new ArrayList<>(), 1),
								new PGoTLANumber("1", 1)),
						new PGoTLACaseArm(
								new PGoTLANumber("2", 1),
								new PGoTLANumber("3", 1)),
					}),
					new PGoTLAVariable("foo", new ArrayList<>(), 1),
					1),
			},
			{"[F EXCEPT !.a = 2]", new PGoTLAFunctionSubstitution(
					new PGoTLAVariable("F", new ArrayList<>(), 1),
					Arrays.asList(new PGoTLAFunctionSubstitutionPair[] {
							new PGoTLAFunctionSubstitutionPair(
									Arrays.asList(new PGoTLASubstitutionKey[] {
											new PGoTLASubstitutionKeyName("a"),
									}),
									new PGoTLANumber("2", 1)),
					}),
					1),
			},
			{"[F EXCEPT ![1] = 2]", new PGoTLAFunctionSubstitution(
					new PGoTLAVariable("F", new ArrayList<>(), 1),
					Arrays.asList(new PGoTLAFunctionSubstitutionPair[] {
							new PGoTLAFunctionSubstitutionPair(
									Arrays.asList(new PGoTLASubstitutionKey[] {
											new PGoTLASubstitutionKeyIndices(Arrays.asList(new PGoTLAExpression[] {
													new PGoTLANumber("1", 1),
											})),
									}),
									new PGoTLANumber("2", 1)),
					}),
					1),
			},
			{"[F EXCEPT !.a[1] = 2]", new PGoTLAFunctionSubstitution(
					new PGoTLAVariable("F", new ArrayList<>(), 1),
					Arrays.asList(new PGoTLAFunctionSubstitutionPair[] {
							new PGoTLAFunctionSubstitutionPair(
									Arrays.asList(new PGoTLASubstitutionKey[] {
											new PGoTLASubstitutionKeyName("a"),
											new PGoTLASubstitutionKeyIndices(Arrays.asList(new PGoTLAExpression[] {
													new PGoTLANumber("1", 1),
											})),
									}),
									new PGoTLANumber("2", 1)),
					}),
					1),
			},
			{"[F EXCEPT !.a[1] = 2, !.b = 3]", new PGoTLAFunctionSubstitution(
					new PGoTLAVariable("F", new ArrayList<>(), 1),
					Arrays.asList(new PGoTLAFunctionSubstitutionPair[] {
							new PGoTLAFunctionSubstitutionPair(
									Arrays.asList(new PGoTLASubstitutionKey[] {
											new PGoTLASubstitutionKeyName("a"),
											new PGoTLASubstitutionKeyIndices(Arrays.asList(new PGoTLAExpression[] {
													new PGoTLANumber("1", 1),
											})),
									}),
									new PGoTLANumber("2", 1)),
							new PGoTLAFunctionSubstitutionPair(
									Arrays.asList(new PGoTLASubstitutionKey[] {
											new PGoTLASubstitutionKeyName("b"),
									}),
									new PGoTLANumber("3", 1)),
					}),
					1),
			},
		});
	}
	
	public String exprString;
	private PGoTLAExpression exprExpected;
	public TLAExpressionParseTest(String exprString, PGoTLAExpression exprExpected) {
		this.exprString = exprString;
		this.exprExpected = exprExpected;
	}

	@Test
	public void test() throws PGoTLAParseException, PGoTLALexerException {
		TLALexer lexer = new TLALexer(Arrays.asList(new String[] {exprString}));
		// don't ignore the expression because it's not in a module
		lexer.requireModule(false);
		
		List<TLAToken> tokens = lexer.readTokens();
		
		PGoTLAExpression expr = TLAParser.readExpression(tokens.listIterator());
		
		assertThat(expr, is(exprExpected));
	}

}
