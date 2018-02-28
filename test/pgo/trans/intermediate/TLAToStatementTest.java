package pgo.trans.intermediate;

import static org.junit.Assert.assertEquals;

import java.util.Vector;

import org.json.JSONObject;
import org.junit.Before;
import org.junit.Test;

import pcal.PcalTranslate;
import pcal.TLAToken;
import pgo.PGoNetOptions;
import pgo.PGoOptionException;
import pgo.model.golang.*;
import pgo.model.intermediate.PGoType;
import pgo.model.intermediate.PGoVariable;
import pgo.model.tla.*;
import pgo.trans.PGoTransException;

/**
 * Test the conversion of parsed TLA asts to Go asts.
 *
 */
public class TLAToStatementTest {
	private Imports imports;
	private PGoTempData data;

	@Before
	public void init() throws PGoOptionException {
		imports = new Imports();
		data = new PGoTempData(PGoTransIntermediateData.buildWith(new PGoNetOptions(new JSONObject())));
	}

	@Test
	public void testBool() throws PGoTransException {
		PGoTLABool tla = new PGoTLABool("TRUE", 0);
		Expression expected = new Token("true");
		assertEquals(expected, new TLAExprToGo(tla, imports, null).toExpression());
		tla = new PGoTLABool("FALSE", 0);
		expected = new Token("false");
		assertEquals(expected, new TLAExprToGo(tla, imports, null).toExpression());
	}

	@Test
	public void testNumber() throws PGoTransException {
		PGoTLANumber tla = new PGoTLANumber("-15", 0);
		Expression expected = new Token("-15");
		assertEquals(expected, new TLAExprToGo(tla, imports, null).toExpression());
	}

	@Test
	public void testString() throws PGoTransException {
		PGoTLAString tla = new PGoTLAString("string", 0);
		Expression expected = new Token("\"string\"");
		assertEquals(expected, new TLAExprToGo(tla, imports, null).toExpression());
	}

	@Test
	public void testArith() throws PGoTransException {
		PGoTLASimpleArithmetic tla = new PGoTLASimpleArithmetic("*", new PGoTLANumber("3", 0),
				new PGoTLAVariable("x", 0), 0);
		data.globals.put("x", PGoVariable.convert("x", PGoType.inferFromGoTypeName("int")));
		Expression expected;
		Expression result = new TLAExprToGo(tla, imports, data).toExpression();
		Vector<Expression> se = new Vector<>();
		se.add(new Token("3"));
		se.add(new Token(" * "));
		se.add(new Token("x"));
		expected = new SimpleExpression(se);
		assertEquals(expected, result);

		tla = new PGoTLASimpleArithmetic("*", new PGoTLANumber("2.5", 0), new PGoTLAVariable("x", 0), 0);
		se.clear();
		se.add(new Token("2.5"));
		se.add(new Token(" * "));
		se.add(new TypeConversion("float64", new Token("x")));
		expected = new SimpleExpression(se);
		result = new TLAExprToGo(tla, imports, data).toExpression();
		assertEquals(expected, result);

		tla = new PGoTLASimpleArithmetic("^", new PGoTLAVariable("y", 0), new PGoTLANumber("5", 0), 0);
		data.globals.put("y", PGoVariable.convert("y", PGoType.inferFromGoTypeName("int")));
		result = new TLAExprToGo(tla, imports, data).toExpression();
		Vector<Expression> params = new Vector<>();
		params.add(new TypeConversion("float64", new Token("y")));
		params.add(new Token("5"));
		expected = new FunctionCall("math.Pow", params);
		assertEquals(expected, result);
	}

	@Test
	public void testGroup() throws PGoTransException {
		PGoTLAGroup tla = new PGoTLAGroup(new Vector<PGoTLA>() {
			{
				add(new PGoTLASimpleArithmetic("*", new PGoTLANumber("3", 0), new PGoTLAVariable("x", 0), 0));
			}
		}, 0);
		data.globals.put("x", PGoVariable.convert("x", PGoType.inferFromGoTypeName("int")));
		Expression expected;
		Expression result = new TLAExprToGo(tla, imports, data).toExpression();
		Vector<Expression> se = new Vector<>();
		se.add(new Token("("));
		se.add(new Token("3"));
		se.add(new Token(" * "));
		se.add(new Token("x"));
		se.add(new Token(")"));
		expected = new SimpleExpression(se);
		assertEquals(expected, result);
	}

	@Test
	public void testArray() throws PGoTransException {
		PGoTLAArray tla = new PGoTLAArray(new Vector<TLAToken>() {
			{
				add(new TLAToken("1", 0, TLAToken.NUMBER));
				add(new TLAToken(",", 0, TLAToken.BUILTIN));
				add(new TLAToken("2", 0, TLAToken.NUMBER));
				add(new TLAToken("+", 0, TLAToken.BUILTIN));
				add(new TLAToken("3", 0, TLAToken.NUMBER));
			}
		}, 0);

		PGoVariable var = PGoVariable.convert("arr", PGoType.inferFromGoTypeName("tuple[int, int]"));
		data.getLocals().put("arr", var);
		Expression result = new TLAExprToGo(tla, imports, data, var).toExpression();

		Vector<Expression> params = new Vector<>();
		params.add(new Token("1"));
		params.add(new SimpleExpression(new Vector<Expression>() {
			{
				add(new Token("2"));
				add(new Token(" + "));
				add(new Token("3"));
			}
		}));
		assertEquals(new FunctionCall("datatypes.NewTuple", params), result);

		var = PGoVariable.convert("channel", PGoType.inferFromGoTypeName("chan[int]"));
		data.getLocals().clear();
		data.getLocals().put("channel", var);
		result = new TLAExprToGo(tla, imports, data, var).toExpression();
		assertEquals(new FunctionCall("datatypes.NewChan", params), result);

		tla = new PGoTLAArray(new Vector<TLAToken>() {
			{
				add(new TLAToken("x", 0, TLAToken.IDENT));
				add(new TLAToken("\\in", 0, TLAToken.BUILTIN));
				add(new TLAToken("S", 0, TLAToken.IDENT));
				add(new TLAToken(",", 0, TLAToken.BUILTIN));
				add(new TLAToken("y", 0, TLAToken.IDENT));
				add(new TLAToken("\\in", 0, TLAToken.BUILTIN));
				add(new TLAToken("T", 0, TLAToken.IDENT));
				add(new TLAToken("|->", 0, TLAToken.BUILTIN));
				add(new TLAToken("x", 0, TLAToken.IDENT));
			}
		}, 0);
		data.getLocals().clear();
		data.getLocals().put("S", PGoVariable.convert("S", PGoType.inferFromGoTypeName("set[set[tuple[int...]]]")));
		data.getLocals().put("T", PGoVariable.convert("T", PGoType.inferFromGoTypeName("set[string]")));
		result = new TLAExprToGo(tla, imports, data).toExpression();
		AnonymousFunction f = new AnonymousFunction(
				PGoType.inferFromGoTypeName("set[tuple[int...]]"),
				new Vector<ParameterDeclaration>() {
					{
						add(new ParameterDeclaration("x", PGoType.inferFromGoTypeName("set[tuple[int...]]")));
						add(new ParameterDeclaration("y", PGoType.inferFromGoTypeName("string")));
					}
				},
				new Vector<>(),
				new Vector<Statement>() {
					{
						add(new Return(new Token("x")));
					}
				});
		params.clear();
		params.add(f);
		params.add(new Token("S"));
		params.add(new Token("T"));
		assertEquals(new FunctionCall("datatypes.MapsTo", params), result);
	}

	@Test
	public void testFunction() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<>();
		toks.add(new TLAToken("3", 0, TLAToken.NUMBER));
		toks.add(new TLAToken(",", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("a", 0, TLAToken.STRING));
		PGoTLAFunctionCall tla = new PGoTLAFunctionCall("foo", toks, 0);
		Vector<Vector<TLAToken>> foo = new Vector<>();
		foo.add(new Vector<>());
		foo.get(0).add(new TLAToken("b", 0, TLAToken.IDENT));
		data.defns.put("foo", new PGoTLADefinition("foo", new Vector<PGoVariable>() {
			{
				add(PGoVariable.convert("a", PGoType.inferFromGoTypeName("int")));
				add(PGoVariable.convert("b", PGoType.inferFromGoTypeName("string")));
			}
		}, PcalTranslate.MakeExpr(foo), null, 0));
		Expression result = new TLAExprToGo(tla, imports, data).toExpression();
		Vector<Expression> se = new Vector<>();
		se.add(new FunctionCall("foo", new Vector<Expression>() {
			{
				add(new Token("3"));
				add(new Token("\"a\""));
			}
		}));
		assertEquals(new SimpleExpression(se), result);

		data.defns.clear();
		data.globals.put("foo",
				PGoVariable.convert("foo", PGoType.inferFromGoTypeName("map[tuple[int, string]]set[int]")));
		result = new TLAExprToGo(tla, imports, data).toExpression();
		se = new Vector<>();
		se.add(new TypeAssertion(new FunctionCall("Get", new Vector<Expression>() {
			{
				add(new FunctionCall("datatypes.NewTuple", new Vector<Expression>() {
					{
						add(new Token("3"));
						add(new Token("\"a\""));
					}
				}));
			}
		}, new Token("foo")), PGoType.inferFromGoTypeName("set[int]")));
		assertEquals(new SimpleExpression(se), result);

		data.globals.clear();
		toks.clear();
		toks.add(new TLAToken("a", 0, TLAToken.IDENT));
		tla = new PGoTLAFunctionCall("Len", toks, 0);
		data.globals.put("a", PGoVariable.convert("a", PGoType.inferFromGoTypeName("string")));
		result = new TLAExprToGo(tla, imports, data).toExpression();
		se = new Vector<>();
		se.add(new FunctionCall("len", new Vector<Expression>() {
			{
				add(new Token("a"));
			}
		}));
		assertEquals(new SimpleExpression(se), result);

		data.globals.clear();
		data.globals.put("a", PGoVariable.convert("a", PGoType.inferFromGoTypeName("tuple[int]")));
		result = new TLAExprToGo(tla, imports, data).toExpression();
		se.set(0, new FunctionCall("Size", new Vector<>(), new Token("a")));
		assertEquals(new SimpleExpression(se), result);

		tla = new PGoTLAFunctionCall("foo", toks, 0);
		data.globals.clear();
		data.globals.put("a", PGoVariable.convert("a", PGoType.inferFromGoTypeName("int")));
		data.globals.put("foo", PGoVariable.convert("foo", PGoType.inferFromGoTypeName("[]string")));
		result = new TLAExprToGo(tla, imports, data).toExpression();
		se.clear();
		se.add(new Token("foo"));
		se.add(new Token("["));
		se.add(new Token("a"));
		se.add(new Token(" - "));
		se.add(new Token("1"));
		se.add(new Token("]"));
		assertEquals(new SimpleExpression(se), result);
	}

	@Test
	public void testSequence() throws PGoTransException {
		PGoTLASequence tla = new PGoTLASequence(new PGoTLANumber("1", 0), new PGoTLAVariable("x", 0), 0);
		data.globals.put("x", PGoVariable.convert("x", PGoType.inferFromGoTypeName("int")));
		Expression expected;
		Vector<Expression> args = new Vector<>();
		args.add(new Token("1"));
		args.add(new Token("x"));
		expected = new FunctionCall("datatypes.Sequence", args);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		data.globals.clear();
		data.globals.put("x", PGoVariable.convert("x", PGoType.inferFromGoTypeName("uint64")));
		args.clear();
		args.add(new Token("1"));
		args.add(new TypeConversion("int", new Token("x")));
		expected = new FunctionCall("datatypes.Sequence", args);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
	}

	@Test
	public void testBoolOp() throws PGoTransException {
		PGoTLABoolOp tla = new PGoTLABoolOp("/=", new PGoTLANumber("2", 0), new PGoTLAVariable("x", 0), 0);
		data.globals.put("x", PGoVariable.convert("x", PGoType.inferFromGoTypeName("int")));
		Vector<Expression> expr = new Vector<>();
		Expression expected;
		expr.add(new Token("2"));
		expr.add(new Token(" != "));
		expr.add(new Token("x"));
		expected = new SimpleExpression(expr);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		tla = new PGoTLABoolOp("\\/", new PGoTLAVariable("y", 0), new PGoTLAVariable("z", 0), 0);
		data.globals.put("y", PGoVariable.convert("y", PGoType.inferFromGoTypeName("bool")));
		data.globals.put("z", PGoVariable.convert("z", PGoType.inferFromGoTypeName("bool")));
		expr.clear();
		expr.add(new Token("y"));
		expr.add(new Token(" || "));
		expr.add(new Token("z"));
		expected = new SimpleExpression(expr);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		tla = new PGoTLABoolOp("#", new PGoTLASet(new Vector<>(), 0), new PGoTLAVariable("S", 0), 0);
		data.globals.put("S", PGoVariable.convert("S", PGoType.inferFromGoTypeName("set[string]")));
		expr.clear();
		expr.add(new Token("!"));
		Vector<Expression> args = new Vector<>();
		args.add(new FunctionCall("datatypes.NewSet", new Vector<>()));
		expr.add(new FunctionCall("Equal", args, new Token("S")));
		expected = new SimpleExpression(expr);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		tla = new PGoTLABoolOp("=<", new PGoTLAVariable("x", 0), new PGoTLAVariable("y", 0), 0);
		data.globals.clear();
		data.globals.put("x", PGoVariable.convert("x", PGoType.inferFromGoTypeName("int")));
		data.globals.put("y", PGoVariable.convert("y", PGoType.inferFromGoTypeName("float64")));
		expr.clear();
		args.clear();
		args.add(new Token("x"));
		expr.add(new FunctionCall("float64", args));
		expr.add(new Token(" <= "));
		expr.add(new Token("y"));
		expected = new SimpleExpression(expr);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
	}

	@Test
	public void testSet() throws PGoTransException {
		PGoTLASet tla = new PGoTLASet(new Vector<>(), 0);
		Expression expected = new FunctionCall("datatypes.NewSet", new Vector<>());
		assertEquals(expected, new TLAExprToGo(tla, imports, null).toExpression());

		Vector<TLAToken> between = new Vector<>();
		between.add(new TLAToken("1", 0, TLAToken.NUMBER));
		between.add(new TLAToken(",", 0, TLAToken.BUILTIN));
		between.add(new TLAToken("x", 0, TLAToken.IDENT));
		data.globals.put("x", PGoVariable.convert("x", PGoType.inferFromGoTypeName("float64")));
		tla = new PGoTLASet(between, 0);
		Vector<Expression> args = new Vector<>();
		args.add(new Token("1"));
		args.add(new Token("x"));
		expected = new FunctionCall("datatypes.NewSet", args);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		between.clear();
		between.add(new TLAToken("x", 0, TLAToken.IDENT));
		between.add(new TLAToken("\\in", 0, TLAToken.BUILTIN));
		between.add(new TLAToken("S", 0, TLAToken.IDENT));
		between.add(new TLAToken(":", 0, TLAToken.BUILTIN));
		between.add(new TLAToken("TRUE", 0, TLAToken.BUILTIN));
		tla = new PGoTLASet(between, 0);
		data.globals.clear();
		data.globals.put("S", PGoVariable.convert("S", PGoType.inferFromGoTypeName("set[set[string]]")));
		AnonymousFunction P = new AnonymousFunction(
				PGoType.inferFromGoTypeName("bool"),
				new Vector<ParameterDeclaration>() {
					{
						add(new ParameterDeclaration("x", PGoType.inferFromGoTypeName("set[string]")));
					}
				},
				new Vector<>(),
				new Vector<Statement>() {
					{
						add(new Return(new Token("true")));
					}
				});
		expected = new FunctionCall("datatypes.SetConstructor", new Vector<Expression>() {
			{
				add(new Token("S"));
				add(P);
			}
		});
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		between.clear();
		between.add(new TLAToken("x", 0, TLAToken.IDENT));
		between.add(new TLAToken("\\union", 0, TLAToken.BUILTIN));
		between.add(new TLAToken("y", 0, TLAToken.IDENT));
		between.add(new TLAToken(":", 0, TLAToken.BUILTIN));
		between.add(new TLAToken("x", 0, TLAToken.IDENT));
		between.add(new TLAToken("\\in", 0, TLAToken.BUILTIN));
		between.add(new TLAToken("S", 0, TLAToken.IDENT));
		between.add(new TLAToken(",", 0, TLAToken.BUILTIN));
		between.add(new TLAToken("y", 0, TLAToken.IDENT));
		between.add(new TLAToken("\\in", 0, TLAToken.BUILTIN));
		between.add(new TLAToken("T", 0, TLAToken.IDENT));
		tla = new PGoTLASet(between, 0);
		data.globals.clear();
		data.globals.put("S", PGoVariable.convert("S", PGoType.inferFromGoTypeName("set[set[float64]]")));
		data.globals.put("T", PGoVariable.convert("T", PGoType.inferFromGoTypeName("set[set[float64]]")));
		AnonymousFunction f = new AnonymousFunction(
				PGoType.inferFromGoTypeName("set[float64]"),
				new Vector<ParameterDeclaration>() {
					{
						add(new ParameterDeclaration("x", PGoType.inferFromGoTypeName("set[float64]")));
						add(new ParameterDeclaration("y", PGoType.inferFromGoTypeName("set[float64]")));
					}
				},
				new Vector<>(),
				new Vector<Statement>() {
					{
						add(new Return(new FunctionCall("Union", new Vector<Expression>() {
							{
								add(new Token("x"));
							}
						}, new Token("y"))));
					}
				});
		expected = new FunctionCall("datatypes.SetImage", new Vector<Expression>() {
			{
				add(f);
				add(new Token("S"));
				add(new Token("T"));
			}
		});
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
	}

	@Test
	public void testSetOp() throws PGoTransException {
		PGoTLASetOp tla = new PGoTLASetOp("\\union", new PGoTLASet(new Vector<>(), 0), new PGoTLAVariable("A", 0), 0);
		data.globals.put("A", PGoVariable.convert("A", PGoType.inferFromGoTypeName("set[int]")));
		Expression expected;
		Vector<Expression> args = new Vector<>();
		args.add(new FunctionCall("datatypes.NewSet", new Vector<>()));
		expected = new FunctionCall("Union", args, new Token("A"));
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		tla = new PGoTLASetOp("\\notin", new PGoTLAVariable("a", 0), new PGoTLASet(new Vector<>(), 0), 0);
		data.globals.put("a", PGoVariable.convert("a", PGoType.inferFromGoTypeName("int")));
		Vector<Expression> se = new Vector<>();
		se.add(new Token("!"));
		args.clear();
		args.add(new Token("a"));
		se.add(new FunctionCall("Contains", args, new FunctionCall("datatypes.NewSet", new Vector<>())));
		expected = new SimpleExpression(se);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
	}

	@Test
	public void testUnary() throws PGoTransException {
		PGoTLAUnary tla = new PGoTLAUnary("\\neg", new PGoTLAVariable("p", 0), 0);
		data.globals.put("p", PGoVariable.convert("p", PGoType.inferFromGoTypeName("bool")));
		Expression expected;
		Vector<Expression> expr = new Vector<>();
		expr.add(new Token("!"));
		expr.add(new Token("p"));
		expected = new SimpleExpression(expr);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		tla = new PGoTLAUnary("SUBSET", new PGoTLAVariable("S", 0), 0);
		data.globals.put("S", PGoVariable.convert("S", PGoType.inferFromGoTypeName("set[int]")));
		expected = new FunctionCall("PowerSet", new Vector<>(), new Token("S"));
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		tla = new PGoTLAUnary("UNION", new PGoTLAVariable("S", 0), 0);
		data.globals.clear();
		data.globals.put("S", PGoVariable.convert("S", PGoType.inferFromGoTypeName("set[set[string]]")));
		expected = new FunctionCall("EltUnion", new Vector<>(), new Token("S"));
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		tla = new PGoTLAUnary("CHOOSE", new PGoTLAVariadic(":", new Vector<PGoTLA>() {
			{
				add(new PGoTLASetOp("\\in", new PGoTLAVariable("x", 0), new PGoTLAVariable("S", 0), 0));
			}
		}, new Vector<TLAToken>() {
			{
				add(new TLAToken("TRUE", 0, TLAToken.BUILTIN, 0));
			}
		}, 0), 0);
		Vector<Expression> params = new Vector<>();
		params.add(new AnonymousFunction(PGoType.inferFromGoTypeName("bool"),
				new Vector<ParameterDeclaration>() {
					{
						add(new ParameterDeclaration("x", PGoType.inferFromGoTypeName("set[string]")));
					}
				},
				new Vector<>(),
				new Vector<Statement>() {
					{
						add(new Return(new Token("true")));
					}
				}));
		params.add(new Token("S"));
		expected = new FunctionCall("datatypes.Choose", params);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		tla = new PGoTLAUnary("\\E", new PGoTLAVariadic(":", new Vector<PGoTLA>() {
			{
				add(new PGoTLASetOp("\\in", new PGoTLAVariable("x", 0), new PGoTLAVariable("S", 0), 0));
				add(new PGoTLASetOp("\\in", new PGoTLAVariable("y", 0), new PGoTLAVariable("T", 0), 0));
			}
		}, new Vector<TLAToken>() {
			{
				add(new TLAToken("x", 0, TLAToken.IDENT, 0));
				add(new TLAToken("*", 0, TLAToken.BUILTIN, 0));
				add(new TLAToken("y", 0, TLAToken.IDENT, 0));
				add(new TLAToken("=", 0, TLAToken.BUILTIN, 0));
				add(new TLAToken("4", 0, TLAToken.NUMBER, 0));
			}
		}, 0), 0);
		data.globals.clear();
		data.globals.put("S", PGoVariable.convert("S", PGoType.inferFromGoTypeName("set[int]")));
		data.globals.put("T", PGoVariable.convert("T", PGoType.inferFromGoTypeName("set[float64]")));
		params = new Vector<>();
		Vector<Expression> retExpr = new Vector<>();
		retExpr.add(new TypeConversion("float64", new Token("x")));
		retExpr.add(new Token(" * "));
		retExpr.add(new Token("y"));
		retExpr.add(new Token(" == "));
		retExpr.add(new Token("4"));
		params.add(new AnonymousFunction(PGoType.inferFromGoTypeName("bool"),
				new Vector<ParameterDeclaration>() {
					{
						add(new ParameterDeclaration("x", PGoType.inferFromGoTypeName("int")));
						add(new ParameterDeclaration("y", PGoType.inferFromGoTypeName("float64")));
					}
				},
				new Vector<>(),
				new Vector<Statement>() {
					{
						add(new Return(new SimpleExpression(retExpr)));
					}
				}));
		params.add(new Token("S"));
		params.add(new Token("T"));
		expected = new FunctionCall("datatypes.Exists", params);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
	}

	@Test
	public void testVar() throws PGoTransException {
		PGoTLAVariable tla = new PGoTLAVariable("varName", 0);
		data.globals.put("varName", PGoVariable.convert("varName", PGoType.inferFromGoTypeName("string")));
		Expression expected = new Token("varName");
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
	}
}
