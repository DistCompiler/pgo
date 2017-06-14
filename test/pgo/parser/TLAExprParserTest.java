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
	
	@Test
	public void testUnaryOps() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<>();
		toks.add(new TLAToken("~", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("b", 0, TLAToken.IDENT));
		Vector<Vector<TLAToken>> v = new Vector<>();
		v.add(toks);
		TLAExpr exp = PcalTranslate.MakeExpr(v);
		Vector<PGoTLA> result = new TLAExprParser(exp, 0).getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLAUnary);
		
		toks = new Vector<>();
		toks.add(new TLAToken("SUBSET", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("{", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("}", 0, TLAToken.BUILTIN));
		v = new Vector<>();
		v.add(toks);
		exp = PcalTranslate.MakeExpr(v);
		result = new TLAExprParser(exp, 0).getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLAUnary);
		assertTrue(((PGoTLAUnary) result.get(0)).getArg() instanceof PGoTLASet);
	}
	
	@Test
	public void testOrderOfOperations() throws PGoTransException {
		// SUBSET A /= B \\union C \\/ ~(5 \\notin {x \\in S : x /\\ y})
		Vector<TLAToken> toks = new Vector<>();
		toks.add(new TLAToken("SUBSET", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("A", 0, TLAToken.IDENT));
		toks.add(new TLAToken("/=", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("B", 0, TLAToken.IDENT));
		toks.add(new TLAToken("\\union", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("C", 0, TLAToken.IDENT));
		toks.add(new TLAToken("\\/", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("~", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("(", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("5", 0, TLAToken.NUMBER));
		toks.add(new TLAToken("\\notin", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("{", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("x", 0, TLAToken.IDENT));
		toks.add(new TLAToken("\\in", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("S", 0, TLAToken.IDENT));
		toks.add(new TLAToken(":", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("x", 0, TLAToken.IDENT));
		toks.add(new TLAToken("/\\", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("y", 0, TLAToken.IDENT));
		toks.add(new TLAToken("}", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken(")", 0, TLAToken.BUILTIN));
		Vector<Vector<TLAToken>> v = new Vector<>();
		v.add(toks);
		TLAExpr exp = PcalTranslate.MakeExpr(v);
		Vector<PGoTLA> result = new TLAExprParser(exp, 0).getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLABoolOp);
		PGoTLABoolOp root = (PGoTLABoolOp) result.get(0);
		assertEquals("\\/", root.getToken());
		assertTrue(root.getLeft() instanceof PGoTLABoolOp);
		PGoTLABoolOp l = (PGoTLABoolOp) root.getLeft();
		assertEquals("/=", l.getToken());
		assertTrue(l.getLeft() instanceof PGoTLAUnary);
		assertTrue(l.getRight() instanceof PGoTLASetOp);
		
		assertTrue(root.getRight() instanceof PGoTLAUnary);
		PGoTLAUnary r = (PGoTLAUnary) root.getRight();
		assertEquals("~", r.getToken());
		assertTrue(r.getArg() instanceof PGoTLAGroup);
		assertTrue(((PGoTLAGroup) r.getArg()).getInner() instanceof PGoTLASetOp);
		PGoTLASetOp rr = (PGoTLASetOp) ((PGoTLAGroup) r.getArg()).getInner();
		assertTrue(rr.getRight() instanceof PGoTLASet);
		PGoTLASet rrr = (PGoTLASet) rr.getRight();
		assertEquals(1, rrr.getContents().size());
		assertTrue(rrr.getContents().get(0) instanceof PGoTLAVariadic);
		PGoTLAVariadic setContents = (PGoTLAVariadic) rrr.getContents().get(0);
		assertTrue(setContents.getExpr() instanceof PGoTLABoolOp);
		assertTrue(setContents.getArgs().size() == 1);
	}
	
	@Test
	public void testSuchThat() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<TLAToken>() {
			{
				add(new TLAToken("CHOOSE", 0, TLAToken.BUILTIN));
				add(new TLAToken("x", 0, TLAToken.IDENT));
				add(new TLAToken("\\in", 0, TLAToken.BUILTIN));
				add(new TLAToken("S", 0, TLAToken.IDENT));
				add(new TLAToken(":", 0, TLAToken.BUILTIN));
				add(new TLAToken("x", 0, TLAToken.IDENT));
				add(new TLAToken("=", 0, TLAToken.BUILTIN));
				add(new TLAToken("2", 0, TLAToken.NUMBER));
			}
		};
		Vector<Vector<TLAToken>> v = new Vector<>();
		v.add(toks);
		TLAExpr expr = PcalTranslate.MakeExpr(v);
		Vector<PGoTLA> result = new TLAExprParser(expr, 0).getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLAUnary);
		PGoTLAUnary choose = (PGoTLAUnary) result.get(0);
		assertTrue(choose.getArg() instanceof PGoTLAVariadic);
		PGoTLAVariadic st = (PGoTLAVariadic) choose.getArg();
		Vector<PGoTLA> sets = st.getArgs();
		assertTrue(sets.size() == 1);
		assertTrue(st.getExpr() instanceof PGoTLABoolOp);
		
		toks = new Vector<TLAToken>() {
			{
				add(new TLAToken("\\E", 0, TLAToken.BUILTIN));
				add(new TLAToken("x", 0, TLAToken.IDENT));
				add(new TLAToken("\\in", 0, TLAToken.BUILTIN));
				add(new TLAToken("S", 0, TLAToken.IDENT));
				add(new TLAToken(",", 0, TLAToken.BUILTIN));
				add(new TLAToken("y", 0, TLAToken.IDENT));
				add(new TLAToken("\\in", 0, TLAToken.BUILTIN));
				add(new TLAToken("T", 0, TLAToken.IDENT));
				add(new TLAToken(":", 0, TLAToken.BUILTIN));
				add(new TLAToken("x", 0, TLAToken.IDENT));
				add(new TLAToken("/\\", 0, TLAToken.BUILTIN));
				add(new TLAToken("y", 0, TLAToken.IDENT));
			}
		};
		v = new Vector<>();
		v.add(toks);
		expr = PcalTranslate.MakeExpr(v);
		result = new TLAExprParser(expr, 0).getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLAUnary);
		PGoTLAUnary exists = (PGoTLAUnary) result.get(0);
		assertTrue(exists.getArg() instanceof PGoTLAVariadic);
		st = (PGoTLAVariadic) exists.getArg();
		sets = st.getArgs();
		assertTrue(sets.size() == 2);
		assertTrue(st.getExpr() instanceof PGoTLABoolOp);
		PGoTLASetOp set = (PGoTLASetOp) st.getArgs().get(1);
		assertEquals("\\in", set.getToken());
		assertTrue(set.getLeft() instanceof PGoTLAVariable);
		assertTrue(set.getRight() instanceof PGoTLAVariable);
		assertEquals("T", ((PGoTLAVariable) set.getRight()).getName());
	}
}
