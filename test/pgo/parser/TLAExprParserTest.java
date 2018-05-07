package pgo.parser;

import org.junit.Test;
import pcal.PcalTranslate;
import pcal.TLAExpr;
import pcal.TLAToken;
import pgo.model.tla.*;
import pgo.trans.PGoTransException;

import java.util.Arrays;
import java.util.List;
import java.util.Vector;

import static org.junit.Assert.*;

public class TLAExprParserTest {

	@Test
	public void testSimpleNumber() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<>();
		toks.add(new TLAToken("1", 0, TLAToken.NUMBER));
		Vector<Vector<TLAToken>> vec = new Vector<>();
		vec.add(toks);
		TLAExpr exp = PcalTranslate.MakeExpr(vec);

		TLAExprParser parser = new TLAExprParser(exp, 0);
		List<PGoTLAExpression> result = parser.getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLANumber);
		PGoTLANumber res = (PGoTLANumber) result.get(0);
		assertEquals("1", res.getVal());
	}

	@Test
	public void testSimpleString() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<>();
		toks.add(new TLAToken("String", 0, TLAToken.STRING));
		Vector<Vector<TLAToken>> vec = new Vector<>();
		vec.add(toks);
		TLAExpr exp = PcalTranslate.MakeExpr(vec);

		TLAExprParser parser = new TLAExprParser(exp, 0);
		List<PGoTLAExpression> result = parser.getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLAString);
		PGoTLAString res = (PGoTLAString) result.get(0);
		assertEquals("String", res.getString());
	}

	@Test
	public void testSimpleBool() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<>();
		toks.add(new TLAToken("TRUE", 0, TLAToken.BUILTIN));
		Vector<Vector<TLAToken>> vec = new Vector<>();
		vec.add(toks);
		TLAExpr exp = PcalTranslate.MakeExpr(vec);

		TLAExprParser parser = new TLAExprParser(exp, 0);
		List<PGoTLAExpression> result = parser.getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLABool);
		PGoTLABool res = (PGoTLABool) result.get(0);
		assertTrue(res.getVal());

		toks.clear();
		toks.add(new TLAToken("FALSE", 0, TLAToken.BUILTIN));
		vec = new Vector<>();
		vec.add(toks);
		exp = PcalTranslate.MakeExpr(vec);

		parser = new TLAExprParser(exp, 0);
		result = parser.getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLABool);
		res = (PGoTLABool) result.get(0);
		assertFalse(res.getVal());
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
		List<PGoTLAExpression> result = new TLAExprParser(exp, 0).getResult();
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
		List<PGoTLAExpression> result = new TLAExprParser(exp, 0).getResult();
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
		List<PGoTLAExpression> result = new TLAExprParser(exp, 0).getResult();
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
		List<PGoTLAExpression> result = new TLAExprParser(exp, 0).getResult();
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
		List<PGoTLAExpression> result = new TLAExprParser(exp, 0).getResult();
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
		assertEquals(1, setContents.getArgs().size());
	}
	
	@Test
	public void testSuchThat() throws PGoTransException {
		List<TLAToken> toks = new Vector<>(Arrays.asList(
				new TLAToken("CHOOSE", 0, TLAToken.BUILTIN),
				new TLAToken("x", 0, TLAToken.IDENT),
				new TLAToken("\\in", 0, TLAToken.BUILTIN),
				new TLAToken("S", 0, TLAToken.IDENT),
				new TLAToken(":", 0, TLAToken.BUILTIN),
				new TLAToken("x", 0, TLAToken.IDENT),
				new TLAToken("=", 0, TLAToken.BUILTIN),
				new TLAToken("2", 0, TLAToken.NUMBER)));
		List<List<TLAToken>> v = new Vector<>();
		v.add(toks);
		TLAExpr expr = PcalTranslate.MakeExpr(new Vector<>(v));
		List<PGoTLAExpression> result = new TLAExprParser(expr, 0).getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLAUnary);
		PGoTLAUnary choose = (PGoTLAUnary) result.get(0);
		assertTrue(choose.getArg() instanceof PGoTLAVariadic);
		PGoTLAVariadic st = (PGoTLAVariadic) choose.getArg();
		List<PGoTLAExpression> sets = st.getArgs();
		assertEquals(1, sets.size());
		assertTrue(st.getExpr() instanceof PGoTLABoolOp);

		toks = new Vector<>(Arrays.asList(
				new TLAToken("\\E", 0, TLAToken.BUILTIN),
				new TLAToken("x", 0, TLAToken.IDENT),
				new TLAToken("\\in", 0, TLAToken.BUILTIN),
				new TLAToken("S", 0, TLAToken.IDENT),
				new TLAToken(",", 0, TLAToken.BUILTIN),
				new TLAToken("y", 0, TLAToken.IDENT),
				new TLAToken("\\in", 0, TLAToken.BUILTIN),
				new TLAToken("T", 0, TLAToken.IDENT),
				new TLAToken(":", 0, TLAToken.BUILTIN),
				new TLAToken("x", 0, TLAToken.IDENT),
				new TLAToken("/\\", 0, TLAToken.BUILTIN),
				new TLAToken("y", 0, TLAToken.IDENT)));
		v = new Vector<>();
		v.add(toks);
		expr = PcalTranslate.MakeExpr(new Vector<>(v));
		result = new TLAExprParser(expr, 0).getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLAUnary);
		PGoTLAUnary exists = (PGoTLAUnary) result.get(0);
		assertTrue(exists.getArg() instanceof PGoTLAVariadic);
		st = (PGoTLAVariadic) exists.getArg();
		sets = st.getArgs();
		assertEquals(2, sets.size());
		assertTrue(st.getExpr() instanceof PGoTLABoolOp);
		PGoTLASetOp set = (PGoTLASetOp) st.getArgs().get(1);
		assertEquals("\\in", set.getToken());
		assertTrue(set.getLeft() instanceof PGoTLAVariable);
		assertTrue(set.getRight() instanceof PGoTLAVariable);
		assertEquals("T", ((PGoTLAVariable) set.getRight()).getName());
	}
	
	@Test
	public void testFuncCall() throws PGoTransException {
		Vector<TLAToken> toks = new Vector<>();
		toks.add(new TLAToken("foo", 0, TLAToken.IDENT));
		toks.add(new TLAToken("(", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("a", 0, TLAToken.IDENT));
		toks.add(new TLAToken(",", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("b", 0, TLAToken.IDENT));
		toks.add(new TLAToken(")", 0, TLAToken.BUILTIN));
		Vector<Vector<TLAToken>> v = new Vector<>();
		v.add(toks);
		TLAExpr expr = PcalTranslate.MakeExpr(v);
		List<PGoTLAExpression> result = new TLAExprParser(expr, 0).getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLAFunctionCall);
		PGoTLAFunctionCall func = (PGoTLAFunctionCall) result.get(0);
		assertEquals("foo", func.getName());
		assertEquals(2, func.getParams().size());
		assertTrue(func.getParams().get(0) instanceof PGoTLAVariable && func.getParams().get(1) instanceof PGoTLAVariable);
		assertEquals("a", ((PGoTLAVariable) func.getParams().get(0)).getName());
		
		toks.set(3, new TLAToken("*", 0, TLAToken.BUILTIN));
		expr = PcalTranslate.MakeExpr(v);
		result = new TLAExprParser(expr, 0).getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLAFunctionCall);
		func = (PGoTLAFunctionCall) result.get(0);
		assertEquals(1, func.getParams().size());
		assertTrue(func.getParams().get(0) instanceof PGoTLASimpleArithmetic);
		
		toks = new Vector<>();
		toks.add(new TLAToken("foo", 0, TLAToken.IDENT));
		toks.add(new TLAToken("[", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("a", 0, TLAToken.IDENT));
		toks.add(new TLAToken(",", 0, TLAToken.BUILTIN));
		toks.add(new TLAToken("b", 0, TLAToken.IDENT));
		toks.add(new TLAToken("]", 0, TLAToken.BUILTIN));
		v = new Vector<>();
		v.add(toks);
		expr = PcalTranslate.MakeExpr(v);
		result = new TLAExprParser(expr, 0).getResult();
		assertEquals(1, result.size());
		assertTrue(result.get(0) instanceof PGoTLAFunctionCall);
		func = (PGoTLAFunctionCall) result.get(0);
		assertEquals("foo", func.getName());
		assertEquals(2, func.getParams().size());
		assertTrue(func.getParams().get(0) instanceof PGoTLAVariable && func.getParams().get(1) instanceof PGoTLAVariable);
		assertEquals("a", ((PGoTLAVariable) func.getParams().get(0)).getName());
	}
}
