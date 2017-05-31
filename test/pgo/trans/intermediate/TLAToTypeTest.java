package pgo.trans.intermediate;

import static org.junit.Assert.*;

import java.util.Vector;

import org.junit.Before;
import org.junit.Test;

import pcal.TLAToken;
import pgo.model.intermediate.PGoType;
import pgo.model.intermediate.PGoVariable;
import pgo.model.tla.*;
import pgo.trans.PGoTransException;
import pgo.trans.intermediate.*;

/**
 * Test the TLAExprToType class.
 *
 */
public class TLAToTypeTest {
	
	private PGoTransIntermediateData data;
	
	@Before
	public void setup() {
		data = new PGoTransIntermediateData();
	}
	
	@Test
	public void testArray() {
		// TODO
	}
	
	@Test
	public void testBool() throws PGoTransException {
		PGoTLABool tla = new PGoTLABool("TRUE", 0);
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoType.inferFromGoTypeName("bool"), result);
	}
	
	@Test
	public void testBoolOp() throws PGoTransException {
		PGoTLABoolOp tla = new PGoTLABoolOp("/\\", new PGoTLABool("TRUE", 0), new PGoTLAVariable("x", 0), 0);
		data.globals.put("x", PGoVariable.convert("x", PGoType.inferFromGoTypeName("bool")));
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoType.inferFromGoTypeName("bool"), result);
	}
	
	@Test
	public void testFunction() {
		// TODO
	}
	
	@Test
	public void testGroup() throws PGoTransException {
		PGoTLAGroup tla = new PGoTLAGroup(new Vector<PGoTLA>() {
			{
				add(new PGoTLANumber("3", 0));
			}
		}, 0);
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoType.inferFromGoTypeName("int"), result);
	}
	
	@Test
	public void testNumber() throws PGoTransException {
		PGoTLANumber tla = new PGoTLANumber("5", 0);
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoType.inferFromGoTypeName("int"), result);
		tla = new PGoTLANumber("3.5", 0);
		result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoType.inferFromGoTypeName("float64"), result);
	}
	
	@Test
	public void testSequence() throws PGoTransException {
		PGoTLASequence tla = new PGoTLASequence(new PGoTLANumber("0", 0), new PGoTLAVariable("x", 0), 0);
		data.globals.put("x", PGoVariable.convert("x", PGoType.inferFromGoTypeName("natural")));
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoType.inferFromGoTypeName("[]int"), result);
	}
	
	@Test
	public void testSet() throws PGoTransException {
		PGoTLASet tla = new PGoTLASet(new Vector<TLAToken>() {
			{
				add(new TLAToken("1", 0, TLAToken.NUMBER, 0));
				add(new TLAToken(",", 0, TLAToken.BUILTIN, 0));
				add(new TLAToken("2", 0, TLAToken.NUMBER, 0));
			}
		}, 0);
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoType.inferFromGoTypeName("set[int]"), result);
		tla = new PGoTLASet(new Vector<TLAToken>() {
			{
				add(new TLAToken("x", 0, TLAToken.IDENT, 0));
				add(new TLAToken("\\in", 0, TLAToken.BUILTIN, 0));
				add(new TLAToken("Nat", 0, TLAToken.IDENT, 0));
				add(new TLAToken(":", 0, TLAToken.BUILTIN, 0));
				add(new TLAToken("TRUE", 0, TLAToken.BUILTIN));
			}
		}, 0);
		result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoType.inferFromGoTypeName("set[natural]"), result);
	}
	
	@Test
	public void testSetOp() throws PGoTransException {
		PGoTLASet set = new PGoTLASet(new Vector<TLAToken>() {
			{
				add(new TLAToken("1", 0, TLAToken.NUMBER, 0));
				add(new TLAToken(",", 0, TLAToken.BUILTIN, 0));
				add(new TLAToken("2", 0, TLAToken.NUMBER, 0));
			}
		}, 0);
		PGoTLASetOp tla = new PGoTLASetOp("\\union", set, new PGoTLAVariable("T", 0), 0);
		data.globals.put("T", PGoVariable.convert("T", PGoType.inferFromGoTypeName("set[int]")));
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoType.inferFromGoTypeName("set[int]"), result);
		
		tla = new PGoTLASetOp("\\in", new PGoTLANumber("3", 0), set, 0);
		result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoType.inferFromGoTypeName("bool"), result);
		
		set = new PGoTLASet(new Vector<>(), 0);
		tla = new PGoTLASetOp("\\intersect", set, new PGoTLAVariable("T", 0), 0);
		result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoType.inferFromGoTypeName("set[int]"), result);
	}
	
	@Test (expected=PGoTransException.class)
	public void testSetOpFail() throws PGoTransException {
		PGoTLASet set = null, set2 = null;
		try {
			set = new PGoTLASet(new Vector<TLAToken>() {
				{
					add(new TLAToken("1", 0, TLAToken.NUMBER, 0));
					add(new TLAToken(",", 0, TLAToken.BUILTIN, 0));
					add(new TLAToken("2", 0, TLAToken.NUMBER, 0));
				}
			}, 0);
			set2 = new PGoTLASet(new Vector<TLAToken>() {
				{
					add(new TLAToken("a", 0, TLAToken.STRING, 0));
				}
			}, 0);
		} catch (PGoTransException e) {
			fail("Unexpected PGoTransException: " + e.getMessage());
		}
		PGoTLASetOp tla = new PGoTLASetOp("\\cup", set, set2, 0);
		PGoType result = new TLAExprToType(tla, data).getType();
		fail("Expected set types set[int] and set[string] to be incompatible");
	}
	
	@Test
	public void testSimpleArith() throws PGoTransException {
		PGoTLASimpleArithmetic tla = new PGoTLASimpleArithmetic("*", new PGoTLANumber("3", 0), new PGoTLANumber("4", 0), 0);
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoType.inferFromGoTypeName("int"), result);
		tla = new PGoTLASimpleArithmetic("/", new PGoTLANumber("3", 0), new PGoTLANumber("4", 0), 0);
		result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoType.inferFromGoTypeName("float64"), result);
		tla = new PGoTLASimpleArithmetic("+", new PGoTLANumber("2", 0), new PGoTLAVariable("x", 0), 0);
		data.globals.put("x", PGoVariable.convert("x", PGoType.inferFromGoTypeName("float64")));
		result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoType.inferFromGoTypeName("float64"), result);
	}
	
	@Test
	public void testString() throws PGoTransException {
		PGoTLAString tla = new PGoTLAString("string", 0);
		assertEquals(PGoType.inferFromGoTypeName("string"), new TLAExprToType(tla, data).getType());
	}
	
	@Test
	public void testSuchThat() throws PGoTransException {
		Vector<PGoTLA> lhs = new Vector<>();
		lhs.add(new PGoTLASetOp("\\in", new PGoTLAVariable("x", 0), new PGoTLAVariable("S", 0), 0));
		Vector<TLAToken> rhs = new Vector<>();
		rhs.add(new TLAToken("TRUE", 0, TLAToken.BUILTIN, 0));
		PGoTLASuchThat tla = new PGoTLASuchThat(lhs, rhs, 0);
		data.globals.put("S", PGoVariable.convert("S", PGoType.inferFromGoTypeName("set[set[int]]")));
		PGoType result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoType.inferFromGoTypeName("set[int]"), result);
		
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
		tla = new PGoTLASuchThat(lhs, rhs, 0);
		data.globals.clear();
		data.globals.put("S", PGoVariable.convert("S", PGoType.inferFromGoTypeName("set[int]")));
		result = new TLAExprToType(tla, data).getType();
		assertEquals(PGoType.inferFromGoTypeName("int"), result);
	}
	
	@Test
	public void testUnary() throws PGoTransException {
		PGoTLAUnary tla = new PGoTLAUnary("~", new PGoTLABool("FALSE", 0), 0);
		assertEquals(PGoType.inferFromGoTypeName("bool"), new TLAExprToType(tla, data).getType());
		
		tla = new PGoTLAUnary("UNION", new PGoTLAVariable("S", 0), 0);
		data.globals.put("S", PGoVariable.convert("S", PGoType.inferFromGoTypeName("set[set[int]]")));
		System.out.println(new TLAExprToType(tla, data).getType().toTypeName());
		assertEquals(PGoType.inferFromGoTypeName("set[int]"), new TLAExprToType(tla, data).getType());
		
		tla = new PGoTLAUnary("SUBSET", new PGoTLAVariable("S", 0), 0);
		assertEquals(PGoType.inferFromGoTypeName("set[set[set[int]]]"), new TLAExprToType(tla, data).getType());
		
		Vector<PGoTLA> lhs = new Vector<>();
		Vector<TLAToken> rhs = new Vector<>();
		lhs.add(new PGoTLASetOp("\\in", new PGoTLAVariable("x", 0), new PGoTLAVariable("S", 0), 0));
		rhs.add(new TLAToken("TRUE", 0, TLAToken.BUILTIN, 0));
		PGoTLASuchThat arg = new PGoTLASuchThat(lhs, rhs, 0);
		tla = new PGoTLAUnary("CHOOSE", arg, 0);
		assertEquals(PGoType.inferFromGoTypeName("set[int]"), new TLAExprToType(tla, data).getType());
	}
	
	@Test
	public void testVar() throws PGoTransException {
		PGoTLAVariable tla = new PGoTLAVariable("A", 0);
		data.globals.put("A", PGoVariable.convert("A", PGoType.inferFromGoTypeName("set[[][]int]")));
		assertEquals(PGoType.inferFromGoTypeName("set[[][]int]"), new TLAExprToType(tla, data).getType());
	}
}
