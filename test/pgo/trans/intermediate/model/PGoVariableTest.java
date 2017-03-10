package pgo.trans.intermediate.model;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import pcal.AST.PVarDecl;
import pcal.AST.VarDecl;
import pcal.PcalParams;
import pcal.TLAToken;

public class PGoVariableTest {

	// Test basic conversion of variables to PGo equivalent
	@Test
	public void testConvertVarDecl() {
		VarDecl var = new VarDecl();
		var.var = "var";
		var.isEq = false;
		var.val = PcalParams.DefaultVarInit();

		PGoVariable p = PGoVariable.convert(var);
		assertEquals(p.getName(), var.var);
		assertEquals(p.getIsSimpleAssignInit(), var.isEq);
		assertEquals(p.getPcalInitBlock().toString(), var.val.toString());

		var.var = "var2";
		p = PGoVariable.convert(var);
		assertEquals(p.getName(), var.var);

		var.isEq = false;
		p = PGoVariable.convert(var);
		assertEquals(p.getIsSimpleAssignInit(), var.isEq);

		var.val.addToken(new TLAToken("blah", 0, TLAToken.STRING));
		p = PGoVariable.convert(var);
		assertEquals(p.getPcalInitBlock().toString(), var.val.toString());
	}

	public void testConvertPVarDecl() {
		PVarDecl var = new PVarDecl();
		var.var = "var";
		var.val = PcalParams.DefaultVarInit();

		PGoVariable p = PGoVariable.convert(var);
		assertEquals(p.getName(), var.var);
		assertEquals(p.getIsSimpleAssignInit(), var.isEq);
		assertEquals(p.getPcalInitBlock().toString(), var.val.toString());

		var.var = "var2";
		p = PGoVariable.convert(var);
		assertEquals(p.getName(), var.var);

		var.val.addToken(new TLAToken("blah", 0, TLAToken.STRING));
		p = PGoVariable.convert(var);
		assertEquals(p.getPcalInitBlock().toString(), var.val.toString());
	}

	public void testConvertString() {
		String var = "var";
		PGoVariable p = PGoVariable.convert(var);
		assertEquals(var, p.getName());
		assertTrue(p.getIsSimpleAssignInit());
		assertEquals(PcalParams.DefaultVarInit().toString(), p.getPcalInitBlock().toString());

		var = "var2";
		p = PGoVariable.convert(var);
		assertEquals(var, p.getName());
		assertTrue(p.getIsSimpleAssignInit());
		assertEquals(PcalParams.DefaultVarInit().toString(), p.getPcalInitBlock().toString());
	}
}
