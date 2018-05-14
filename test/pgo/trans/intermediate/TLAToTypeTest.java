package pgo.trans.intermediate;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.*;

import org.junit.Before;
import org.junit.Test;

import pcal.PcalTranslate;
import pcal.TLAToken;
import pgo.model.intermediate.PGoCollectionType.PGoChan;
import pgo.model.intermediate.PGoCollectionType.PGoMap;
import pgo.model.intermediate.PGoCollectionType.PGoTuple;
import pgo.model.intermediate.PGoPrimitiveType.PGoDecimal;
import pgo.model.intermediate.PGoPrimitiveType.PGoInt;
import pgo.model.intermediate.PGoPrimitiveType.PGoString;
import pgo.model.intermediate.PGoVariable;
import pgo.model.tla.*;
import pgo.model.type.*;
import pgo.trans.PGoTransException;
import pgo.util.PGoTypeUtil;

/**
 * Test the TLAExprToType class.
 *
 */
public class TLAToTypeTest {

	private PGoTempData data;

	@Before
	public void setup() {
		data = new PGoTempData(new PGoTransIntermediateData());
	}

	@Test
	public void testArray() throws PGoTransException {
		PGoTLAArray tla = new PGoTLAArray(
				new Vector<>(Arrays.asList(
						new TLAToken("1", 0, TLAToken.NUMBER),
						new TLAToken(",", 0, TLAToken.BUILTIN),
						new TLAToken("2", 0, TLAToken.NUMBER),
						new TLAToken("+", 0, TLAToken.BUILTIN),
						new TLAToken("3", 0, TLAToken.NUMBER))),
				0);
		PGoVariable var = PGoVariable.convert("arr", new PGoTypeTuple(Arrays.asList(PGoTypeInt.getInstance(), PGoTypeDecimal.getInstance())));
		data.getLocals().put("arr", var);

		PGoType result = new TLAExprToType(tla, data).getType();
		data.solver.accept(new PGoTypeConstraint(var.getType(), result, tla.getLine()));
		result = PGoTypeUtil.unifyAndSubstitute(data.solver, result).realize();
		assertTrue(result instanceof PGoTypeTuple);
		assertEquals(2, ((PGoTypeTuple) result).getElementTypes().size());
		assertTrue(((PGoTypeTuple) result).getElementTypes().get(1) instanceof PGoTypeDecimal);

		var = PGoVariable.convert("channel", new PGoTypeChan(PGoTypeInt.getInstance()));
		data.getLocals().clear();
		data.getLocals().put("channel", var);
		result = new TLAExprToType(tla, data).getType();
		data.solver.accept(new PGoTypeConstraint(result, var.getType(), tla.getLine()));
		result = PGoTypeUtil.unifyAndSubstitute(data.solver, result).realize();
		assertTrue(result instanceof PGoTypeChan);
		assertEquals(PGoTypeInt.getInstance(), ((PGoTypeChan) result).getElementType());

		tla = new PGoTLAArray(
				new Vector<>(Arrays.asList(
						new TLAToken("x", 0, TLAToken.IDENT),
						new TLAToken("\\in", 0, TLAToken.BUILTIN),
						new TLAToken("S", 0, TLAToken.IDENT),
						new TLAToken(",", 0, TLAToken.BUILTIN),
						new TLAToken("y", 0, TLAToken.IDENT),
						new TLAToken("\\in", 0, TLAToken.BUILTIN),
						new TLAToken("T", 0, TLAToken.IDENT),
						new TLAToken("|->", 0, TLAToken.BUILTIN),
						new TLAToken("x", 0, TLAToken.IDENT))),
				0);
		data.getLocals().clear();
		data.getLocals().put("S", PGoVariable.convert("S", new PGoTypeSet(new PGoTypeSet(new PGoTypeSlice(PGoTypeInt.getInstance())))));
		data.getLocals().put("T", PGoVariable.convert("T", new PGoTypeSet(PGoTypeString.getInstance())));
		result = new TLAExprToType(tla, data).getType();
		data.solver.accept(new PGoTypeConstraint(
				result,
				new PGoTypeMap(
						new PGoTypeTuple(Arrays.asList(
								new PGoTypeSet(new PGoTypeSlice(PGoTypeInt.getInstance())),
								PGoTypeString.getInstance())),
						new PGoTypeSet(new PGoTypeSlice(PGoTypeInt.getInstance()))),
				tla.getLine()));
		result = PGoTypeUtil.unifyAndSubstitute(data.solver, result).realize();
		assertTrue(result instanceof PGoTypeMap);
		assertEquals(new PGoTypeTuple(Arrays.asList(new PGoTypeSet(new PGoTypeSlice(PGoTypeInt.getInstance())), PGoTypeString.getInstance())), ((PGoTypeMap) result).getKeyType());
		assertEquals(new PGoTypeSet(new PGoTypeSlice(PGoTypeInt.getInstance())), ((PGoTypeMap) result).getValueType());
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void testArrayFail() throws PGoTransException {
		PGoTLAArray tla = new PGoTLAArray(
				new Vector<>(Arrays.asList(
						new TLAToken("1", 0, TLAToken.NUMBER),
						new TLAToken(",", 0, TLAToken.BUILTIN),
						new TLAToken("2", 0, TLAToken.NUMBER),
						new TLAToken("+", 0, TLAToken.BUILTIN),
						new TLAToken("3", 0, TLAToken.NUMBER))),
				0);
		PGoVariable var = PGoVariable.convert("arr", new PGoTypeTuple(Arrays.asList(PGoTypeInt.getInstance(), PGoTypeString.getInstance())));
		data.getLocals().put("arr", var);
		PGoType result = new TLAExprToType(tla, data).getType();
		data.solver.accept(new PGoTypeConstraint(var.getType(), result, tla.getLine()));
		PGoTypeUtil.unifyAndSubstitute(data.solver, result);
	}

	@Test
	public void testBool() throws PGoTransException {
		PGoTLABool tla = new PGoTLABool("TRUE", 0);
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoTypeBool.getInstance(), result);
	}

	@Test
	public void testBoolOp() throws PGoTransException {
		PGoTLABoolOp tla = new PGoTLABoolOp("/\\", new PGoTLABool("TRUE", 0), new PGoTLAVariable("x", 0), 0);
		data.globals.put("x", PGoVariable.convert("x", PGoTypeBool.getInstance()));
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoTypeBool.getInstance(), result);
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void testAndOrFail() throws PGoTransException {
		PGoTLABoolOp tla = new PGoTLABoolOp("\\/", new PGoTLABool("FALSE", 0), new PGoTLANumber("3", 0), 0);
		PGoTypeUtil.unifyAndSubstitute(data.solver, new TLAExprToType(tla, data).getType());
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void testComparatorFail() throws PGoTransException {
		PGoTLABoolOp tla = new PGoTLABoolOp("<=", new PGoTLAVariable("x", 0), new PGoTLANumber("1.5", 0), 0);
		data.globals.put("x", PGoVariable.convert("x", PGoTypeBool.getInstance()));
		PGoTypeUtil.unifyAndSubstitute(data.solver, new TLAExprToType(tla, data).getType());
	}

	@Test
	public void testStringFunction() throws PGoTransException {
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
		PGoType result = new TLAExprToType(tla, data).getType();
		data.solver.unify();
		data.solver.simplify();
		assertEquals(PGoTypeString.getInstance(), result.substitute(data.solver.getMapping()));
	}

	@Test
	public void testIntFunction() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<>();
		toks.add(new TLAToken("3", 0, TLAToken.NUMBER));
		toks.add(new TLAToken(",", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("a", 0, TLAToken.STRING));
		PGoTLAFunctionCall tla = new PGoTLAFunctionCall("foo", toks, 0);
		Vector<Vector<TLAToken>> foo = new Vector<>();
		foo.add(new Vector<>());
		foo.get(0).add(new TLAToken("b", 0, TLAToken.IDENT));
		data.globals.put("foo",
				PGoVariable.convert(
						"foo",
						new PGoTypeMap(
								new PGoTypeTuple(
										Arrays.asList(PGoTypeInt.getInstance(),
												PGoTypeString.getInstance())),
								new PGoTypeSet(PGoTypeInt.getInstance()))));
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(new PGoTypeSet(PGoTypeInt.getInstance()), PGoTypeUtil.unifyAndSubstitute(data.solver, result));
	}

	@Test
	public void testIntFunction2() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<>();
		toks.add(new TLAToken("a", 0, TLAToken.IDENT));
		PGoTLAFunctionCall tla = new PGoTLAFunctionCall("Len", toks, 0);
		data.globals.put("a", PGoVariable.convert("a", PGoTypeString.getInstance()));
		PGoType result = new TLAExprToType(tla, data).getType();
		assertTrue(result instanceof PGoTypeInt);
	}

	@Test
	public void testIntStringFunction() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<>(Collections.singletonList(new TLAToken("a", 0, TLAToken.IDENT)));
		PGoTLAFunctionCall tla = new PGoTLAFunctionCall("Len", toks, 0);
		data.globals.put("a", PGoVariable.convert("a", new PGoTypeTuple(Collections.singletonList(PGoTypeInt.getInstance()))));
		PGoType result = new TLAExprToType(tla, data).getType();
		assertTrue(result instanceof PGoTypeInt);

		tla = new PGoTLAFunctionCall("foo", toks, 0);
		data.globals.clear();
		data.globals.put("a", PGoVariable.convert("a", PGoTypeInt.getInstance()));
		data.globals.put("foo", PGoVariable.convert("foo", new PGoTypeSlice(PGoTypeString.getInstance())));
		result = new TLAExprToType(tla, data).getType();
		assertTrue(result instanceof PGoTypeString);
	}

	@Test
	public void testGroup() throws PGoTransException {
		PGoTLAGroup tla = new PGoTLAGroup(Collections.singletonList(new PGoTLANumber("3", 0)), 0);
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoTypeInt.getInstance(), result.realize());
	}

	@Test
	public void testNumber() throws PGoTransException {
		PGoTLANumber tla = new PGoTLANumber("5", 0);
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoTypeInt.getInstance(), result.realize());
		tla = new PGoTLANumber("3.5", 0);
		result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoTypeDecimal.getInstance(), result.realize());
	}

	@Test
	public void testSequence() throws PGoTransException {
		PGoTLASequence tla = new PGoTLASequence(new PGoTLANumber("-1", 0), new PGoTLAVariable("x", 0), 0);
		data.globals.put("x", PGoVariable.convert("x", PGoTypeNatural.getInstance()));
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(new PGoTypeSet(PGoTypeInt.getInstance()), PGoTypeUtil.unifyAndSubstitute(data.solver, result).realize());
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void testSequenceFail() throws PGoTransException {
		PGoTLASequence tla = new PGoTLASequence(new PGoTLANumber("-1", 0), new PGoTLAVariable("x", 0), 0);
		data.globals.put("x", PGoVariable.convert("x", PGoTypeDecimal.getInstance()));
		PGoTypeUtil.unifyAndSubstitute(data.solver, new TLAExprToType(tla, data).getType());
	}

	@Test
	public void testSet() throws PGoTransException {
		PGoTLASet tla = new PGoTLASet(
				new Vector<>(Arrays.asList(
						new TLAToken("1", 0, TLAToken.NUMBER, 0),
						new TLAToken(",", 0, TLAToken.BUILTIN, 0),
						new TLAToken("2", 0, TLAToken.NUMBER, 0))),
				0);
		PGoType result = new TLAExprToType(tla, data).getType();
		data.solver.unify();
		data.solver.simplify();
		assertEquals(new PGoTypeSet(PGoTypeInt.getInstance()), result.substitute(data.solver.getMapping()));
		tla = new PGoTLASet(
				new Vector<>(Arrays.asList(
						new TLAToken("x", 0, TLAToken.IDENT, 0),
						new TLAToken("\\in", 0, TLAToken.BUILTIN, 0),
						new TLAToken("Nat", 0, TLAToken.IDENT, 0),
						new TLAToken(":", 0, TLAToken.BUILTIN, 0),
						new TLAToken("TRUE", 0, TLAToken.BUILTIN))),
				0);
		result = new TLAExprToType(tla, data).getType();
		assertEquals(new PGoTypeSet(PGoTypeNatural.getInstance()), PGoTypeUtil.unifyAndSubstitute(data.solver, result).realize());
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void testSetFail() throws PGoTransException {
		PGoTLASet tla = new PGoTLASet(
				new Vector<>(Arrays.asList(
						new TLAToken("1", 0, TLAToken.NUMBER, 0),
						new TLAToken(",", 0, TLAToken.BUILTIN, 0),
						new TLAToken("2.5", 0, TLAToken.NUMBER, 0),
						new TLAToken(",", 0, TLAToken.BUILTIN, 0),
						new TLAToken("x", 0, TLAToken.IDENT, 0))),
				0);
		data.globals.put("x", PGoVariable.convert("x", new PGoTypeUnrealizedNumber()));
		try {
			PGoType result = new TLAExprToType(tla, data).getType();
			assertEquals(new PGoTypeSet(PGoTypeDecimal.getInstance()), PGoTypeUtil.unifyAndSubstitute(data.solver, result).realize());
		} catch (PGoTransException e) {
			fail("Unexpected PGoTransException");
		}
		tla = new PGoTLASet(
				new Vector<>(Arrays.asList(
						new TLAToken("1", 0, TLAToken.NUMBER, 0),
						new TLAToken(",", 0, TLAToken.BUILTIN, 0),
						new TLAToken("2.5", 0, TLAToken.NUMBER, 0),
						new TLAToken(",", 0, TLAToken.BUILTIN, 0),
						new TLAToken("TRUE", 0, TLAToken.BUILTIN, 0))),
				0);
		PGoTypeUtil.unifyAndSubstitute(data.solver, new TLAExprToType(tla, data).getType());
	}

	@Test
	public void testSetOp() throws PGoTransException {
		PGoTLASet set = new PGoTLASet(
				new Vector<>(Arrays.asList(
						new TLAToken("1", 0, TLAToken.NUMBER, 0),
						new TLAToken(",", 0, TLAToken.BUILTIN, 0),
						new TLAToken("2.5", 0, TLAToken.NUMBER, 0))),
				0);
		PGoTLASetOp tla = new PGoTLASetOp("\\union", set, new PGoTLAVariable("T", 0), 0);
		data.globals.put("T", PGoVariable.convert("T", new PGoTypeSet(PGoTypeDecimal.getInstance())));
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(new PGoTypeSet(PGoTypeDecimal.getInstance()), PGoTypeUtil.unifyAndSubstitute(data.solver, result).realize());

		tla = new PGoTLASetOp("\\in", new PGoTLANumber("3", 0), set, 0);
		result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoTypeBool.getInstance(), PGoTypeUtil.unifyAndSubstitute(data.solver, result));

		set = new PGoTLASet(new Vector<TLAToken>(), 0);
		tla = new PGoTLASetOp("\\intersect", set, new PGoTLAVariable("T", 0), 0);
		result = new TLAExprToType(tla, data).getType();
		assertEquals(new PGoTypeSet(PGoTypeDecimal.getInstance()), PGoTypeUtil.unifyAndSubstitute(data.solver, result).realize());
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void testSetOpFail() throws PGoTransException {
		PGoTLASet set = null, set2 = null;
		try {
			set = new PGoTLASet(
					new Vector<>(Arrays.asList(
							new TLAToken("1", 0, TLAToken.NUMBER, 0),
							new TLAToken(",", 0, TLAToken.BUILTIN, 0),
							new TLAToken("2", 0, TLAToken.NUMBER, 0)))
					,
					0);
			set2 = new PGoTLASet(
					new Vector<>(Collections.singletonList(new TLAToken("a", 0, TLAToken.STRING, 0))),
					0);
		} catch (PGoTransException e) {
			fail("Unexpected PGoTransException: " + e.getMessage());
		}
		PGoTLASetOp tla = new PGoTLASetOp("\\cup", set, set2, 0);
		PGoType result = new TLAExprToType(tla, data).getType();
		PGoTypeUtil.unifyAndSubstitute(data.solver, result);
		fail("Expected set types set[int] and set[string] to be incompatible");
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void testSetInFail() throws PGoTransException {
		PGoTLAVariable l = new PGoTLAVariable("l", 0), r = new PGoTLAVariable("r", 0);
		data.globals.put("l", PGoVariable.convert("l", PGoTypeString.getInstance()));
		data.globals.put("r", PGoVariable.convert("r", new PGoTypeSet(new PGoTypeSet(PGoTypeString.getInstance()))));
		PGoTLASetOp tla = new PGoTLASetOp("\\in", l, r, 0);
		PGoType type = new TLAExprToType(tla, data).getType();
		PGoTypeUtil.unifyAndSubstitute(data.solver, type);
	}

	@Test
	public void testSimpleArith() throws PGoTransException {
		PGoTLASimpleArithmetic tla = new PGoTLASimpleArithmetic("*", new PGoTLANumber("3", 0), new PGoTLANumber("4", 0),
				0);
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoTypeNatural.getInstance(), result.realize());
		tla = new PGoTLASimpleArithmetic("/", new PGoTLANumber("3", 0), new PGoTLANumber("4", 0), 0);
		result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoTypeDecimal.getInstance(), result.realize());
		tla = new PGoTLASimpleArithmetic("+", new PGoTLANumber("2", 0), new PGoTLAVariable("x", 0), 0);
		data.globals.put("x", PGoVariable.convert("x", PGoTypeDecimal.getInstance()));
		result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoTypeDecimal.getInstance(), PGoTypeUtil.unifyAndSubstitute(data.solver, result).realize());
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void testSimpleArithFail() throws PGoTransException {
		PGoTLAExpression tla = new PGoTLASimpleArithmetic("+", new PGoTLAString("string", 0), new PGoTLAVariable("x", 0), 0);
		data.globals.put("x", PGoVariable.convert("x", PGoTypeString.getInstance()));
		PGoTypeUtil.unifyAndSubstitute(data.solver, new TLAExprToType(tla, data).getType());
	}

	@Test
	public void testString() throws PGoTransException {
		PGoTLAString tla = new PGoTLAString("string", 0);
		assertEquals(PGoTypeString.getInstance(), PGoTypeUtil.unifyAndSubstitute(data.solver, new TLAExprToType(tla, data).getType()));
	}

	@Test
	public void testSuchThat() throws PGoTransException {
		Vector<PGoTLAExpression> lhs = new Vector<>();
		lhs.add(new PGoTLASetOp("\\in", new PGoTLAVariable("x", 0), new PGoTLAVariable("S", 0), 0));
		Vector<TLAToken> rhs = new Vector<>();
		rhs.add(new TLAToken("TRUE", 0, TLAToken.BUILTIN, 0));
		PGoTLAVariadic tla = new PGoTLAVariadic(":", lhs, rhs, 0);
		data.globals.put("S", PGoVariable.convert("S", new PGoTypeSet(new PGoTypeSet(PGoTypeInt.getInstance()))));
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(new PGoTypeSet(PGoTypeInt.getInstance()), PGoTypeUtil.unifyAndSubstitute(data.solver, result).realize());

		lhs = new Vector<>();
		lhs.add(new PGoTLASimpleArithmetic("*", new PGoTLAVariable("x", 0), new PGoTLAVariable("y", 0), 0));
		rhs = new Vector<>();
		rhs.add(new TLAToken("x", 0, TLAToken.IDENT, 0));
		rhs.add(new TLAToken("\\in", 0, TLAToken.BUILTIN, 0));
		rhs.add(new TLAToken("S", 0, TLAToken.IDENT, 0));
		rhs.add(new TLAToken(",", 0, TLAToken.BUILTIN, 0));
		rhs.add(new TLAToken("y", 0, TLAToken.IDENT, 0));
		rhs.add(new TLAToken("\\in", 0, TLAToken.BUILTIN, 0));
		rhs.add(new TLAToken("S", 0, TLAToken.IDENT, 0));
		tla = new PGoTLAVariadic(":", lhs, rhs, 0);
		data.globals.clear();
		data.globals.put("S", PGoVariable.convert("S", new PGoTypeSet(PGoTypeInt.getInstance())));
		result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoTypeInt.getInstance(), PGoTypeUtil.unifyAndSubstitute(data.solver, result).realize());
	}

	@Test
	public void testUnary() throws PGoTransException {
		PGoTLAUnary tla = new PGoTLAUnary("~", new PGoTLABool("FALSE", 0), 0);
		assertEquals(PGoTypeBool.getInstance(), new TLAExprToType(tla, data).getType());

		tla = new PGoTLAUnary("UNION", new PGoTLAVariable("S", 0), 0);
		data.globals.put("S", PGoVariable.convert("S", new PGoTypeSet(new PGoTypeSet(PGoTypeInt.getInstance()))));
		assertEquals(new PGoTypeSet(PGoTypeInt.getInstance()),
				PGoTypeUtil.unifyAndSubstitute(data.solver, new TLAExprToType(tla, data).getType()).realize());

		tla = new PGoTLAUnary("SUBSET", new PGoTLAVariable("S", 0), 0);
		assertEquals(
				new PGoTypeSet(new PGoTypeSet(new PGoTypeSet(PGoTypeInt.getInstance()))),
				PGoTypeUtil.unifyAndSubstitute(data.solver, new TLAExprToType(tla, data).getType()).realize());

		Vector<PGoTLAExpression> lhs = new Vector<>();
		Vector<TLAToken> rhs = new Vector<>();
		lhs.add(new PGoTLASetOp("\\in", new PGoTLAVariable("x", 0), new PGoTLAVariable("S", 0), 0));
		rhs.add(new TLAToken("TRUE", 0, TLAToken.BUILTIN, 0));
		PGoTLAVariadic arg = new PGoTLAVariadic(":", lhs, rhs, 0);
		tla = new PGoTLAUnary("CHOOSE", arg, 0);
		assertEquals(new PGoTypeSet(PGoTypeInt.getInstance()), PGoTypeUtil.unifyAndSubstitute(data.solver, new TLAExprToType(tla, data).getType()).realize());
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void testEltUnionFail() throws PGoTransException {
		PGoTLAUnary tla = new PGoTLAUnary("UNION", new PGoTLAVariable("S", 0), 0);
		data.globals.put("S", PGoVariable.convert("S", new PGoTypeSet(new PGoTypeSlice(PGoTypeInt.getInstance()))));
		PGoTypeUtil.unifyAndSubstitute(data.solver, new TLAExprToType(tla, data).getType());
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void testPowersetFail() throws PGoTransException {
		PGoTLAUnary tla = new PGoTLAUnary("SUBSET", new PGoTLAVariable("S", 0), 0);
		data.globals.put("S", PGoVariable.convert("S", new PGoTypeMap(PGoTypeString.getInstance(), PGoTypeInt.getInstance())));
		PGoTypeUtil.unifyAndSubstitute(data.solver, new TLAExprToType(tla, data).getType());
	}

	@Test(expected = PGoTypeUnificationException.class)
	public void testNegateFail() throws PGoTransException {
		PGoTLAUnary tla = new PGoTLAUnary("~", new PGoTLANumber("3", 0), 0);
		PGoTypeUtil.unifyAndSubstitute(data.solver, new TLAExprToType(tla, data).getType());
	}

	@Test
	public void testVar() throws PGoTransException {
		PGoTLAVariable tla = new PGoTLAVariable("A", 0);
		data.globals.put("A", PGoVariable.convert("A", new PGoTypeSet(new PGoTypeSlice(new PGoTypeSlice(PGoTypeInt.getInstance())))));
		assertEquals(new PGoTypeSet(new PGoTypeSlice(new PGoTypeSlice(PGoTypeInt.getInstance()))), new TLAExprToType(tla, data).getType());
	}
}
