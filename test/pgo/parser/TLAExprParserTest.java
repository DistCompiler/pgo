package pgo.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.Vector;

import org.junit.Test;

import pcal.PcalTranslate;
import pcal.TLAExpr;
import pcal.TLAToken;
import pgo.model.tla.*;
import pgo.trans.PGoTransException;

public class TLAExprParserTest {

	@Test
	public void testSimpleNumber() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<TLAToken>();
		toks.add(new TLAToken("1", 0, TLAToken.NUMBER));
		Vector<Vector<TLAToken>> vec = new Vector<Vector<TLAToken>>();
		vec.add(toks);
		TLAExpr exp = PcalTranslate.MakeExpr(vec);

		TLAExprParser parser = new TLAExprParser(exp, 0);
		Vector<PGoTLA> result = parser.getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLANumber);
		PGoTLANumber res = (PGoTLANumber) result.get(0);
		assertEquals("1", res.getVal());
	}

	@Test
	public void testSimpleString() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<TLAToken>();
		toks.add(new TLAToken("String", 0, TLAToken.STRING));
		Vector<Vector<TLAToken>> vec = new Vector<Vector<TLAToken>>();
		vec.add(toks);
		TLAExpr exp = PcalTranslate.MakeExpr(vec);

		TLAExprParser parser = new TLAExprParser(exp, 0);
		Vector<PGoTLA> result = parser.getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLAString);
		PGoTLAString res = (PGoTLAString) result.get(0);
		assertEquals("String", res.getString());
	}

	@Test
	public void testSimpleBool() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<TLAToken>();
		toks.add(new TLAToken("TRUE", 0, TLAToken.BUILTIN));
		Vector<Vector<TLAToken>> vec = new Vector<Vector<TLAToken>>();
		vec.add(toks);
		TLAExpr exp = PcalTranslate.MakeExpr(vec);

		TLAExprParser parser = new TLAExprParser(exp, 0);
		Vector<PGoTLA> result = parser.getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLABool);
		PGoTLABool res = (PGoTLABool) result.get(0);
		assertEquals(true, res.getVal());

		toks.clear();
		toks.add(new TLAToken("FALSE", 0, TLAToken.BUILTIN));
		vec = new Vector<Vector<TLAToken>>();
		vec.add(toks);
		exp = PcalTranslate.MakeExpr(vec);

		parser = new TLAExprParser(exp, 0);
		result = parser.getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLABool);
		res = (PGoTLABool) result.get(0);
		assertEquals(false, res.getVal());
	}

	@Test
	public void testArithmetic() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<>();
		toks.add(new TLAToken("a", 0, TLAToken.IDENT));
		toks.add(new TLAToken("+", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("b", 0, TLAToken.IDENT));
		toks.add(new TLAToken("^", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("3", 0, TLAToken.NUMBER));
		Vector<Vector<TLAToken>> v = new Vector<>();
		v.add(toks);
		TLAExpr exp = PcalTranslate.MakeExpr(v);
		Vector<PGoTLA> result = new TLAExprParser(exp, 0).getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLASimpleArithmetic);
		PGoTLASimpleArithmetic sa = (PGoTLASimpleArithmetic) result.get(0);
		assertTrue(sa.getLeft() instanceof PGoTLAVariable);
		assertTrue(sa.getRight() instanceof PGoTLASimpleArithmetic);
		assertTrue(((PGoTLASimpleArithmetic) sa.getRight()).getLeft() instanceof PGoTLAVariable);
		assertTrue(((PGoTLASimpleArithmetic) sa.getRight()).getRight() instanceof PGoTLANumber);
	}
	
	@Test
	public void testSetOps() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<>();
		toks.add(new TLAToken("1", 0, TLAToken.NUMBER));
		toks.add(new TLAToken("\\in", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("A", 0, TLAToken.IDENT));
		toks.add(new TLAToken("\\union", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("B", 0, TLAToken.IDENT));
		Vector<Vector<TLAToken>> v = new Vector<>();
		v.add(toks);
		TLAExpr exp = PcalTranslate.MakeExpr(v);
		Vector<PGoTLA> result = new TLAExprParser(exp, 0).getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLASetOp);
		PGoTLASetOp so = (PGoTLASetOp) result.get(0);
		assertTrue(so.getLeft() instanceof PGoTLANumber);
		assertTrue(so.getRight() instanceof PGoTLASetOp);		
	}
	
	@Test
	public void testBoolOps() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<>();
		toks.add(new TLAToken("(", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("p", 0, TLAToken.IDENT));
		toks.add(new TLAToken("/\\", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("TRUE", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken(")", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("/=", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("q", 0, TLAToken.IDENT));
		Vector<Vector<TLAToken>> v = new Vector<>();
		v.add(toks);
		TLAExpr exp = PcalTranslate.MakeExpr(v);
		Vector<PGoTLA> result = new TLAExprParser(exp, 0).getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLABoolOp);
		PGoTLABoolOp bo = (PGoTLABoolOp) result.get(0);
		assertTrue(bo.getLeft() instanceof PGoTLAGroup);
		assertTrue(bo.getRight() instanceof PGoTLAVariable);
		assertEquals("/=", bo.getToken());
		PGoTLABoolOp lhs = (PGoTLABoolOp) ((PGoTLAGroup) bo.getLeft()).getInner();
		assertTrue(lhs.getRight() instanceof PGoTLABool);
	}
	// TODO more tests
}
