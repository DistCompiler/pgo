package pgo.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.Vector;

import org.junit.Test;

import pcal.PcalTranslate;
import pcal.TLAExpr;
import pcal.TLAToken;
import pgo.model.tla.PGoTLA;
import pgo.model.tla.PGoTLABool;
import pgo.model.tla.PGoTLANumber;
import pgo.model.tla.PGoTLAString;
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

	// TODO more tests
}
