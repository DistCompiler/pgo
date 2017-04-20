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

public class PGoTransIntermediateDataTest {

	private PGoTransIntermediateData d;

	@Before
	public void SetUp() {
		d = new PGoTransIntermediateData();
		for (int i = 0; i < 10; i++) {
			d.globals.put("var" + i, PGoVariable.convert("var" + i));
			Procedure p = new Procedure();
			p.params = new Vector();
			p.decls = new Vector();
			PVarDecl pv = new PVarDecl();
			pv.var = "OtherVar" + i;
			p.decls.add(pv);
			p.name = "func" + i;

			d.funcs.put("func" + i, PGoFunction.convert(p));
		}
		for (int i = 0; i < 10; i++) {
			Procedure p = new Procedure();
			p.params = new Vector();
			p.name = "PGoOtherFunc" + i;
			p.decls = new Vector();
			PVarDecl pv = new PVarDecl();
			pv.var = "OtherOtherVar" + i;
			p.decls.add(pv);
			d.funcs.put("PGoOtherFunc" + i, PGoFunction.convert(p));
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
		
		for (int i = 0; i < 10; i++) {
			f = d.findPGoFunction("PGoOtherFunc" + i);
			assertNotNull(f);
			assertEquals("PGoOtherFunc" + i, f.getName());
			assertNull(d.funcs.get("OtherFunc" + i));
			assertNotNull(d.funcs.get("PGoOtherFunc" + i));
			
			f = d.findPGoFunction("OtherFunc" + i);
			assertNotNull(f);
			assertEquals("OtherFunc" + i, f.getName());
			assertNotNull(d.funcs.get("OtherFunc" + i));
			assertNull(d.funcs.get("PGoOtherFunc" + i));
		}
	}
}
