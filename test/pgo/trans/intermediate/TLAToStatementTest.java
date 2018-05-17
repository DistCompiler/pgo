package pgo.trans.intermediate;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Vector;

import org.json.JSONObject;
import org.junit.Before;
import org.junit.Test;

import pcal.PcalTranslate;
import pcal.TLAToken;
import pgo.PGoNetOptions;
import pgo.PGoOptionException;
import pgo.model.golang.*;
import pgo.model.intermediate.PGoVariable;
import pgo.model.tla.*;
import pgo.model.type.*;
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
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
		tla = new PGoTLABool("FALSE", 0);
		expected = new Token("false");
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
	}

	@Test
	public void testNumber() throws PGoTransException {
		PGoTLANumber tla = new PGoTLANumber("-15", 0);
		Expression expected = new Token("-15");
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
	}

	@Test
	public void testString() throws PGoTransException {
		PGoTLAString tla = new PGoTLAString("string", 0);
		Expression expected = new Token("\"string\"");
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
	}

	@Test
	public void testArith() throws PGoTransException {
		PGoTLASimpleArithmetic tla = new PGoTLASimpleArithmetic("*", new PGoTLANumber("3", 0),
				new PGoTLAVariable("x", 0), 0);
		data.globals.put("x", PGoVariable.convert("x", PGoTypeInt.getInstance()));
		new TLAExprToType(tla, data);
		data.solver.unify();
		data.solver.simplify();
		Expression result = new TLAExprToGo(tla, imports, data).toExpression();
		Vector<Expression> se = new Vector<>();
		se.add(new Token("3"));
		se.add(new Token(" * "));
		se.add(new Token("x"));
		Expression expected = new SimpleExpression(se);
		assertEquals(expected, result);

		tla = new PGoTLASimpleArithmetic("*", new PGoTLANumber("2.5", 0), new PGoTLAVariable("x", 0), 0);
		se.clear();
		se.add(new Token("2.5"));
		se.add(new Token(" * "));
		se.add(new TypeConversion(PGoTypeDecimal.getInstance(), new Token("x")));
		expected = new SimpleExpression(se);
		new TLAExprToType(tla, data);
		data.solver.simplify();
		data.solver.unify();
		result = new TLAExprToGo(tla, imports, data).toExpression();
		assertEquals(expected, result);

		tla = new PGoTLASimpleArithmetic("^", new PGoTLAVariable("y", 0), new PGoTLANumber("5", 0), 0);
		data.globals.put("y", PGoVariable.convert("y", PGoTypeInt.getInstance()));
		new TLAExprToType(tla, data);
		data.solver.simplify();
		data.solver.unify();
		result = new TLAExprToGo(tla, imports, data).toExpression();
		Vector<Expression> params = new Vector<>();
		params.add(new TypeConversion(PGoTypeDecimal.getInstance(), new Token("y")));
		params.add(new Token("5"));
		expected = new FunctionCall("math.Pow", params);
		assertEquals(expected, result);
	}

	@Test
	public void testGroup() throws PGoTransException {
		PGoTLAGroup tla = new PGoTLAGroup(
				Collections.singletonList(new PGoTLASimpleArithmetic(
						"*", new PGoTLANumber("3", 0), new PGoTLAVariable("x", 0), 0))
				, 0);
		data.globals.put("x", PGoVariable.convert("x", PGoTypeInt.getInstance()));
		new TLAExprToType(tla, data);
		data.solver.unify();
		data.solver.simplify();
		Expression result = new TLAExprToGo(tla, imports, data).toExpression();
		Vector<Expression> se = new Vector<>();
		se.add(new Token("("));
		se.add(new Token("3"));
		se.add(new Token(" * "));
		se.add(new Token("x"));
		se.add(new Token(")"));
		Expression expected = new SimpleExpression(se);
		assertEquals(expected, result);
	}

	@Test
	public void testTuple() throws PGoTransException {
		PGoTLAArray tla = new PGoTLAArray(
				new Vector<>(Arrays.asList(
						new TLAToken("1", 0, TLAToken.NUMBER),
						new TLAToken(",", 0, TLAToken.BUILTIN),
						new TLAToken("2", 0, TLAToken.NUMBER),
						new TLAToken("+", 0, TLAToken.BUILTIN),
						new TLAToken("3", 0, TLAToken.NUMBER)))
				, 0);

		PGoVariable var = PGoVariable.convert("arr", new PGoTypeTuple(Arrays.asList(PGoTypeInt.getInstance(), PGoTypeInt.getInstance())));
		data.getLocals().put("arr", var);
		data.solver.accept(new PGoTypeConstraint(var.getType(), new TLAExprToType(tla, data).getType(), tla.getLine()));
		data.solver.unify();
		data.solver.simplify();
		Expression result = new TLAExprToGo(tla, imports, data).toExpression();

		Vector<Expression> params = new Vector<>();
		params.add(new Token("1"));
		params.add(new SimpleExpression(Arrays.asList(
				new Token("2"),
				new Token(" + "),
				new Token("3"))));
		assertEquals(new FunctionCall("datatypes.NewTuple", params), result);
	}

	@Test
	public void testChannel() throws PGoTransException {
		PGoTLAArray tla = new PGoTLAArray(
				new Vector<>(Arrays.asList(
						new TLAToken("1", 0, TLAToken.NUMBER),
						new TLAToken(",", 0, TLAToken.BUILTIN),
						new TLAToken("2", 0, TLAToken.NUMBER),
						new TLAToken("+", 0, TLAToken.BUILTIN),
						new TLAToken("3", 0, TLAToken.NUMBER)))
				, 0);
		PGoVariable var = PGoVariable.convert("channel", new PGoTypeChan(PGoTypeInt.getInstance()));
		data.getLocals().put("channel", var);
		data.solver.accept(new PGoTypeConstraint(var.getType(), new TLAExprToType(tla, data).getType(), tla.getLine()));
		data.solver.unify();
		data.solver.simplify();
		Expression result = new TLAExprToGo(tla, imports, data).toExpression();

		Vector<Expression> params = new Vector<>();
		params.add(new Token("1"));
		params.add(new SimpleExpression(Arrays.asList(
				new Token("2"),
				new Token(" + "),
				new Token("3"))));
		assertEquals(new FunctionCall("datatypes.NewChan", params), result);
	}

	@Test
	public void testComprehension() throws PGoTransException {
		PGoTLAArray tla = new PGoTLAArray(
				new Vector<>(Arrays.asList(
						new TLAToken("x", 0, TLAToken.IDENT),
						new TLAToken("\\in", 0, TLAToken.BUILTIN),
						new TLAToken("S", 0, TLAToken.IDENT),
						new TLAToken(",", 0, TLAToken.BUILTIN),
						new TLAToken("y", 0, TLAToken.IDENT),
						new TLAToken("\\in", 0, TLAToken.BUILTIN),
						new TLAToken("T", 0, TLAToken.IDENT),
						new TLAToken("|->", 0, TLAToken.BUILTIN),
						new TLAToken("x", 0, TLAToken.IDENT)))
				, 0);
		PGoVariable var = PGoVariable.convert(
				"comprehension",
				new PGoTypeMap(
						new PGoTypeTuple(Arrays.asList(
								new PGoTypeSet(new PGoTypeSlice(PGoTypeInt.getInstance())),
								PGoTypeString.getInstance())),
						new PGoTypeSet(new PGoTypeSlice(PGoTypeInt.getInstance()))));
		data.getLocals().put("comprehension", var);
		data.getLocals().put("S", PGoVariable.convert("S", new PGoTypeSet(new PGoTypeSet(new PGoTypeSlice(PGoTypeInt.getInstance())))));
		data.getLocals().put("T", PGoVariable.convert("T", new PGoTypeSet(PGoTypeString.getInstance())));
		data.solver.accept(new PGoTypeConstraint(var.getType(), new TLAExprToType(tla, data).getType(), tla.getLine()));
		data.solver.unify();
		data.solver.simplify();
		Expression result = new TLAExprToGo(tla, imports, data).toExpression();
		AnonymousFunction f = new AnonymousFunction(
				new PGoTypeSet(new PGoTypeSlice(PGoTypeInt.getInstance())),
				Arrays.asList(
						new ParameterDeclaration("x", new PGoTypeSet(new PGoTypeSlice(PGoTypeInt.getInstance()))),
						new ParameterDeclaration("y", PGoTypeString.getInstance())),
				new Vector<>(),
				Collections.singletonList(new Return(new Token("x"))));
		Vector<Expression> params = new Vector<>();
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
		data.defns.put("foo", new PGoTLADefinition("foo",
				Arrays.asList(
						PGoVariable.convert("a", PGoTypeInt.getInstance()),
						PGoVariable.convert("b", PGoTypeString.getInstance())),
				PcalTranslate.MakeExpr(foo), null, 0));
		Expression result = new TLAExprToGo(tla, imports, data).toExpression();
		Vector<Expression> se = new Vector<>();
		se.add(new FunctionCall("foo", Arrays.asList(new Token("3"), new Token("\"a\""))));
		assertEquals(new SimpleExpression(se), result);
	}

	@Test
	public void testFunction2() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<>();
		toks.add(new TLAToken("3", 0, TLAToken.NUMBER));
		toks.add(new TLAToken(",", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("a", 0, TLAToken.STRING));
		PGoTLAFunctionCall tla = new PGoTLAFunctionCall("foo", toks, 0);
		data.globals.put("foo",
				PGoVariable.convert("foo", new PGoTypeMap(new PGoTypeTuple(Arrays.asList(PGoTypeInt.getInstance(), PGoTypeString.getInstance())), new PGoTypeSet(PGoTypeInt.getInstance()))));
		Expression result = new TLAExprToGo(tla, imports, data).toExpression();
		Vector<Expression> se = new Vector<>();
		se.add(new TypeAssertion(new FunctionCall("Get",
				Collections.singletonList(new FunctionCall(
						"datatypes.NewTuple",
						Arrays.asList(new Token("3"), new Token("\"a\"")))),
				new Token("foo")),
				new PGoTypeSet(PGoTypeInt.getInstance())));
		assertEquals(new SimpleExpression(se), result);
	}

	@Test
	public void testFunction3() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<>();
		toks.add(new TLAToken("a", 0, TLAToken.IDENT));
		PGoTLAFunctionCall tla = new PGoTLAFunctionCall("Len", toks, 0);
		data.globals.put("a", PGoVariable.convert("a", PGoTypeString.getInstance()));
		Expression result = new TLAExprToGo(tla, imports, data).toExpression();
		Vector<Expression> se = new Vector<>();
		se.add(new FunctionCall("len", Collections.singletonList(new Token("a"))));
		assertEquals(new SimpleExpression(se), result);
	}

	@Test
	public void testFunction4() throws PGoTransException {
		data.globals.put("a", PGoVariable.convert("a", new PGoTypeTuple(Collections.singletonList(PGoTypeInt.getInstance()))));
		Vector<TLAToken> toks = new Vector<>();
		toks.add(new TLAToken("a", 0, TLAToken.IDENT));
		PGoTLAFunctionCall tla = new PGoTLAFunctionCall("Len", toks, 0);
		Expression result = new TLAExprToGo(tla, imports, data).toExpression();
		Vector<Expression> se = new Vector<>();
		se.add(new FunctionCall("Size", new Vector<>(), new Token("a")));
		assertEquals(new SimpleExpression(se), result);
	}

	@Test
	public void testFunction5() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<>();
		toks.add(new TLAToken("a", 0, TLAToken.IDENT));
		PGoTLAFunctionCall tla = new PGoTLAFunctionCall("foo", toks, 0);
		data.globals.put("a", PGoVariable.convert("a", PGoTypeInt.getInstance()));
		data.globals.put("foo", PGoVariable.convert("foo", new PGoTypeSlice(PGoTypeString.getInstance())));
		Expression result = new TLAExprToGo(tla, imports, data).toExpression();
		Vector<Expression> se = new Vector<>();
		se.add(new Token("foo"));
		se.add(new Token("["));
		se.add(new Token("a"));
		se.add(new Token(" - "));
		se.add(new Token("1"));
		se.add(new Token("]"));
		assertEquals(new SimpleExpression(se), result);
	}

	@Test
	public void testIntSequence() throws PGoTransException {
		PGoTLASequence tla = new PGoTLASequence(new PGoTLANumber("1", 0), new PGoTLAVariable("x", 0), 0);
		data.globals.put("x", PGoVariable.convert("x", PGoTypeInt.getInstance()));
		List<Expression> args = Arrays.asList(new Token("1"), new Token("x"));
		Expression expected = new FunctionCall("datatypes.Sequence", args);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
	}

	@Test
	public void testNaturalSequence() throws PGoTransException {
		PGoTLASequence tla = new PGoTLASequence(new PGoTLANumber("1", 0), new PGoTLAVariable("x", 0), 0);
		data.globals.put("x", PGoVariable.convert("x", PGoTypeNatural.getInstance()));
		List<Expression> args = Arrays.asList(new Token("1"), new TypeConversion(PGoTypeInt.getInstance(), new Token("x")));
		Expression expected = new FunctionCall("datatypes.Sequence", args);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
	}

	@Test
	public void testBoolOp() throws PGoTransException {
		PGoTLABoolOp tla = new PGoTLABoolOp("/=", new PGoTLANumber("2", 0), new PGoTLAVariable("x", 0), 0);
		data.globals.put("x", PGoVariable.convert("x", PGoTypeInt.getInstance()));
		Vector<Expression> expr = new Vector<>();
		Expression expected;
		expr.add(new Token("2"));
		expr.add(new Token(" != "));
		expr.add(new Token("x"));
		expected = new SimpleExpression(expr);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		tla = new PGoTLABoolOp("\\/", new PGoTLAVariable("y", 0), new PGoTLAVariable("z", 0), 0);
		data.globals.put("y", PGoVariable.convert("y", PGoTypeBool.getInstance()));
		data.globals.put("z", PGoVariable.convert("z", PGoTypeBool.getInstance()));
		expr.clear();
		expr.add(new Token("y"));
		expr.add(new Token(" || "));
		expr.add(new Token("z"));
		expected = new SimpleExpression(expr);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		tla = new PGoTLABoolOp("#", new PGoTLASet(new Vector<TLAToken>(), 0), new PGoTLAVariable("S", 0), 0);
		data.globals.put("S", PGoVariable.convert("S", new PGoTypeSet(PGoTypeString.getInstance())));
		expr.clear();
		expr.add(new Token("!"));
		Vector<Expression> args = new Vector<>();
		args.add(new FunctionCall("datatypes.NewSet", new Vector<>()));
		expr.add(new FunctionCall("Equal", args, new Token("S")));
		expected = new SimpleExpression(expr);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		tla = new PGoTLABoolOp("=<", new PGoTLAVariable("x", 0), new PGoTLAVariable("y", 0), 0);
		data.globals.clear();
		data.globals.put("x", PGoVariable.convert("x", PGoTypeInt.getInstance()));
		data.globals.put("y", PGoVariable.convert("y", PGoTypeDecimal.getInstance()));
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
		PGoTLASet tla = new PGoTLASet(new Vector<TLAToken>(), 0);
		Expression expected = new FunctionCall("datatypes.NewSet", new Vector<>());
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
	}

	@Test
	public void testSet2() throws PGoTransException {
		Vector<TLAToken> between = new Vector<>();
		between.add(new TLAToken("1", 0, TLAToken.NUMBER));
		between.add(new TLAToken(",", 0, TLAToken.BUILTIN));
		between.add(new TLAToken("x", 0, TLAToken.IDENT));
		data.globals.put("x", PGoVariable.convert("x", PGoTypeDecimal.getInstance()));
		PGoTLASet tla = new PGoTLASet(between, 0);
		Vector<Expression> args = new Vector<>();
		args.add(new Token("1"));
		args.add(new Token("x"));
		Expression expected = new FunctionCall("datatypes.NewSet", args);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
	}

	@Test
	public void testSet3() throws PGoTransException {
		Vector<TLAToken> between = new Vector<>();
		between.add(new TLAToken("x", 0, TLAToken.IDENT));
		between.add(new TLAToken("\\in", 0, TLAToken.BUILTIN));
		between.add(new TLAToken("S", 0, TLAToken.IDENT));
		between.add(new TLAToken(":", 0, TLAToken.BUILTIN));
		between.add(new TLAToken("TRUE", 0, TLAToken.BUILTIN));
		PGoTLASet tla = new PGoTLASet(between, 0);
		data.globals.put("S", PGoVariable.convert("S", new PGoTypeSet(new PGoTypeSet(PGoTypeString.getInstance()))));
		AnonymousFunction P = new AnonymousFunction(
				PGoTypeBool.getInstance(),
				Collections.singletonList(new ParameterDeclaration("x", new PGoTypeSet(PGoTypeString.getInstance()))),
				new Vector<>(),
				Collections.singletonList(new Return(new Token("true"))));
		Expression expected = new FunctionCall("datatypes.SetConstructor", Arrays.asList(new Token("S"), P));
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
	}

	@Test
	public void testSet4() throws PGoTransException {
		Vector<TLAToken> between = new Vector<>();
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
		PGoTLASet tla = new PGoTLASet(between, 0);
		data.globals.put("S", PGoVariable.convert("S", new PGoTypeSet(new PGoTypeSet(PGoTypeDecimal.getInstance()))));
		data.globals.put("T", PGoVariable.convert("T", new PGoTypeSet(new PGoTypeSet(PGoTypeDecimal.getInstance()))));
		AnonymousFunction f = new AnonymousFunction(
				new PGoTypeSet(PGoTypeDecimal.getInstance()),
				Arrays.asList(
						new ParameterDeclaration("x", new PGoTypeSet(PGoTypeDecimal.getInstance())),
						new ParameterDeclaration("y", new PGoTypeSet(PGoTypeDecimal.getInstance()))),
				new Vector<>(),
				Collections.singletonList(new Return(new FunctionCall(
						"Union",
						Collections.singletonList(new Token("x")),
						new Token("y")))));
		Expression expected = new FunctionCall("datatypes.SetImage", Arrays.asList(f, new Token("S"), new Token("T")));
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
	}

	@Test
	public void testSetOp() throws PGoTransException {
		PGoTLASetOp tla = new PGoTLASetOp("\\union", new PGoTLASet(new Vector<TLAToken>(), 0), new PGoTLAVariable("A", 0), 0);
		data.globals.put("A", PGoVariable.convert("A", new PGoTypeSet(PGoTypeInt.getInstance())));
		Expression expected;
		Vector<Expression> args = new Vector<>();
		args.add(new FunctionCall("datatypes.NewSet", new Vector<>()));
		expected = new FunctionCall("Union", args, new Token("A"));
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		tla = new PGoTLASetOp("\\notin", new PGoTLAVariable("a", 0), new PGoTLASet(new Vector<TLAToken>(), 0), 0);
		data.globals.put("a", PGoVariable.convert("a", PGoTypeInt.getInstance()));
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
		data.globals.put("p", PGoVariable.convert("p", PGoTypeBool.getInstance()));
		Expression expected;
		Vector<Expression> expr = new Vector<>();
		expr.add(new Token("!"));
		expr.add(new Token("p"));
		expected = new SimpleExpression(expr);
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		tla = new PGoTLAUnary("SUBSET", new PGoTLAVariable("S", 0), 0);
		data.globals.put("S", PGoVariable.convert("S", new PGoTypeSet(PGoTypeInt.getInstance())));
		expected = new FunctionCall("PowerSet", new Vector<>(), new Token("S"));
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		tla = new PGoTLAUnary("UNION", new PGoTLAVariable("S", 0), 0);
		data.globals.clear();
		data.globals.put("S", PGoVariable.convert("S", new PGoTypeSet(new PGoTypeSet(PGoTypeString.getInstance()))));
		expected = new FunctionCall("EltUnion", new Vector<>(), new Token("S"));
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		data.globals.clear();
		data.globals.put("S", PGoVariable.convert("S", new PGoTypeSet(PGoTypeString.getInstance())));
		
		tla = new PGoTLAUnary("CHOOSE", new PGoTLAVariadic(":",
				Collections.singletonList(new PGoTLASetOp("\\in", new PGoTLAVariable("x", 0), new PGoTLAVariable("S", 0), 0)),
				Collections.singletonList(new TLAToken("TRUE", 0, TLAToken.BUILTIN, 0)), 0), 0);
		Vector<Expression> params = new Vector<>();
		params.add(new AnonymousFunction(PGoTypeBool.getInstance(),
				Collections.singletonList(new ParameterDeclaration("x", PGoTypeString.getInstance())),
				new Vector<>(),
				Collections.singletonList(new Return(new Token("true")))));
		params.add(new Token("S"));
		expected = new FunctionCall("datatypes.Choose", params);
		new TLAExprToType(tla, data);
		data.solver.unify();
		data.solver.simplify();
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());

		tla = new PGoTLAUnary("\\E", new PGoTLAVariadic(":",
				Arrays.asList(
						new PGoTLASetOp("\\in", new PGoTLAVariable("x", 0), new PGoTLAVariable("S", 0), 0),
						new PGoTLASetOp("\\in", new PGoTLAVariable("y", 0), new PGoTLAVariable("T", 0), 0)),
				Arrays.asList(
						new TLAToken("x", 0, TLAToken.IDENT, 0),
						new TLAToken("*", 0, TLAToken.BUILTIN, 0),
						new TLAToken("y", 0, TLAToken.IDENT, 0),
						new TLAToken("=", 0, TLAToken.BUILTIN, 0),
						new TLAToken("4", 0, TLAToken.NUMBER, 0)),0), 0);
		data.globals.clear();
		data.globals.put("S", PGoVariable.convert("S", new PGoTypeSet(PGoTypeInt.getInstance())));
		data.globals.put("T", PGoVariable.convert("T", new PGoTypeSet(PGoTypeDecimal.getInstance())));
		params = new Vector<>();
		Vector<Expression> retExpr = new Vector<>();
		retExpr.add(new TypeConversion(PGoTypeDecimal.getInstance(), new Token("x")));
		retExpr.add(new Token(" * "));
		retExpr.add(new Token("y"));
		retExpr.add(new Token(" == "));
		retExpr.add(new Token("4"));
		params.add(new AnonymousFunction(PGoTypeBool.getInstance(),
				Arrays.asList(
						new ParameterDeclaration("x", PGoTypeInt.getInstance()),
						new ParameterDeclaration("y", PGoTypeDecimal.getInstance())),
				new Vector<>(),
				Collections.singletonList(new Return(new SimpleExpression(retExpr)))));
		params.add(new Token("S"));
		params.add(new Token("T"));
		expected = new FunctionCall("datatypes.Exists", params);
		new TLAExprToType(tla, data);
		data.solver.unify();
		data.solver.simplify();
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
	}

	@Test
	public void testVar() throws PGoTransException {
		PGoTLAVariable tla = new PGoTLAVariable("varName", 0);
		data.globals.put("varName", PGoVariable.convert("varName", PGoTypeString.getInstance()));
		Expression expected = new Token("varName");
		assertEquals(expected, new TLAExprToGo(tla, imports, data).toExpression());
	}
}
