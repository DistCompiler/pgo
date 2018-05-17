package pgo.trans.intermediate;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;

import java.util.Vector;

import org.junit.Before;
import org.junit.Test;

import pcal.AST.PVarDecl;
import pcal.AST.Procedure;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoVariable;
import pgo.model.type.PGoTypeGenerator;

public class PGoTransIntermediateDataTest {

	private PGoTransIntermediateData d;
	private PGoTypeGenerator generator;

	@Before
	public void SetUp() {
		d = new PGoTransIntermediateData();
		generator = new PGoTypeGenerator("test");
		for (int i = 0; i < 10; i++) {
			d.globals.put("var" + i, PGoVariable.convert("var" + i, generator.get()));
			Procedure p = new Procedure();
			p.params = new Vector();
			p.decls = new Vector();
			PVarDecl pv = new PVarDecl();
			pv.var = "OtherVar" + i;
			p.decls.add(pv);
			p.name = "func" + i;

			d.funcs.put("func" + i, PGoFunction.convert(p, generator));
		}
		for (int i = 0; i < 10; i++) {
			Procedure p = new Procedure();
			p.params = new Vector();
			p.name = "PGoOtherFunc" + i;
			p.decls = new Vector();
			PVarDecl pv = new PVarDecl();
			pv.var = "OtherOtherVar" + i;
			p.decls.add(pv);
			d.funcs.put("PGoOtherFunc" + i, PGoFunction.convert(p, generator));
		}
	}

	@Test
	public void testFindVariable() {
		assertNull(d.findPGoVariable("random"));
		PGoVariable v;
		for (int i = 0; i < 10; i++) {

			v = d.findPGoVariable("var" + i);
			assertNotNull(v);
			assertEquals("var" + i, v.getName());
		}

		for (int i = 0; i < 10; i++) {
			v = d.findPGoVariable("OtherVar" + i);
			assertNotNull(v);
			assertEquals("OtherVar" + i, v.getName());

			v = d.findPGoVariable("OtherOtherVar" + i);
			assertNotNull(v);
			assertEquals("OtherOtherVar" + i, v.getName());
		}

		assertNotNull(d.findPGoVariable("func1.OtherVar1"));
		assertNull(d.findPGoFunction("func2.OtherVar1"));
	}

	@Test
	public void testFindFunction() {
		assertNull(d.findPGoFunction("random"));
		PGoFunction f;
		for (int i = 0; i < 10; i++) {

			f = d.findPGoFunction("func" + i);
			assertNotNull(f);
			assertEquals("func" + i, f.getName());
		}
	}
}
