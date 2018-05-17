package pgo.model.intermediate;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import pcal.AST.PVarDecl;
import pcal.AST.VarDecl;
import pcal.PcalParams;
import pcal.TLAToken;
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeGenerator;
import pgo.model.type.PGoTypeInt;
import pgo.model.type.PGoTypeString;

public class PGoVariableTest {
	private static PGoTypeGenerator generator = new PGoTypeGenerator("test");

	// Test basic conversion of variables to PGo equivalent
	@Test
	public void testConvertVarDecl() {
		VarDecl var = new VarDecl();
		var.var = "var";
		var.isEq = false;
		var.val = PcalParams.DefaultVarInit();

		PGoVariable p = PGoVariable.convert(var, generator.get());
		assertEquals(p.getName(), var.var);
		assertEquals(p.getIsSimpleAssignInit(), var.isEq);
		assertEquals(p.getPcalInitBlock().toString(), var.val.toString());

		var.var = "var2";
		p = PGoVariable.convert(var, generator.get());
		assertEquals(p.getName(), var.var);

		var.isEq = false;
		p = PGoVariable.convert(var, generator.get());
		assertEquals(p.getIsSimpleAssignInit(), var.isEq);

		var.val.addToken(new TLAToken("blah", 0, TLAToken.STRING));
		p = PGoVariable.convert(var, generator.get());
		assertEquals(p.getPcalInitBlock().toString(), var.val.toString());
	}

	@Test
	public void testConvertPVarDecl() {
		PVarDecl var = new PVarDecl();
		var.var = "var";
		var.val = PcalParams.DefaultVarInit();

		PGoVariable p = PGoVariable.convert(var, generator.get());
		assertEquals(p.getName(), var.var);
		assertEquals(p.getIsSimpleAssignInit(), var.isEq);
		assertEquals(p.getPcalInitBlock().toString(), var.val.toString());

		var.var = "var2";
		p = PGoVariable.convert(var, generator.get());
		assertEquals(p.getName(), var.var);

		var.val.addToken(new TLAToken("blah", 0, TLAToken.STRING));
		p = PGoVariable.convert(var, generator.get());
		assertEquals(p.getPcalInitBlock().toString(), var.val.toString());
	}

	@Test
	public void testConvertString() {
		String var = "var";
		PGoVariable p = PGoVariable.convert(var, generator.get());
		assertEquals(var, p.getName());
		assertTrue(p.getIsSimpleAssignInit());
		assertEquals(PcalParams.DefaultVarInit().toString(), p.getPcalInitBlock().toString());

		var = "var2";
		p = PGoVariable.convert(var, generator.get());
		assertEquals(var, p.getName());
		assertTrue(p.getIsSimpleAssignInit());
		assertEquals(PcalParams.DefaultVarInit().toString(), p.getPcalInitBlock().toString());
	}
	
	@Test
	public void testConvertType() {
		String var = "var";
		PGoType t = PGoTypeInt.getInstance();
		PGoVariable p = PGoVariable.convert(var, t);
		assertEquals(var, p.getName());
		assertEquals(t, p.getType());
		assertTrue(p.getIsSimpleAssignInit());
		assertEquals(PcalParams.DefaultVarInit().toString(), p.getPcalInitBlock().toString());

		var = "var2";
		t = PGoTypeInt.getInstance();
		p = PGoVariable.convert(var, t);
		assertEquals(var, p.getName());
		assertEquals(t, p.getType());
		assertTrue(p.getIsSimpleAssignInit());
		assertEquals(PcalParams.DefaultVarInit().toString(), p.getPcalInitBlock().toString());

		t = PGoTypeString.getInstance();
		p = PGoVariable.convert(var, t);
		assertEquals(var, p.getName());
		assertEquals(t, p.getType());
		assertTrue(p.getIsSimpleAssignInit());
		assertEquals(PcalParams.DefaultVarInit().toString(), p.getPcalInitBlock().toString());
	}
}
