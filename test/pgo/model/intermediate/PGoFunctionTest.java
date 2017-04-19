package pgo.model.intermediate;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.Vector;

import org.junit.Test;

import pcal.AST;
import pcal.AST.LabeledStmt;
import pcal.AST.Macro;
import pcal.AST.PVarDecl;
import pcal.AST.PrintS;
import pcal.AST.Procedure;
import pcal.AST.Process;
import pcal.AST.Skip;
import pcal.PcalParams;

public class PGoFunctionTest {

	// Test basic conversion of procedure to PGo equivalent
	@Test
	public void testConvertProcedure() {
		Procedure p = new Procedure();
		p.name = "proc1";
		PVarDecl param = new PVarDecl();
		param.var = "param1";
		p.params = new Vector<PVarDecl>();
		p.params.add(param);
		p.decls = new Vector<PVarDecl>();
		p.body = new Vector<LabeledStmt>();

		PGoFunction f = PGoFunction.convert(p);
		assertEquals(PGoFunction.FunctionType.Normal, f.getType());
		assertEquals(p.name, f.getName());
		assertEquals(1, f.getParams().size());
		assertParam(f, "param1");
		assertEquals(0, f.getVariables().size());

		assertEquals(p.body.size(), f.getBody().size());
		for (int i = 0; i < f.getBody().size(); i++) {
			assertEquals(p.body.get(i).toString(), f.getBody().get(i).toString());
		}

		p.name = "proc2";
		f = PGoFunction.convert(p);
		assertEquals(p.name, f.getName());
		assertEquals(PGoFunction.FunctionType.Normal, f.getType());
		assertEquals(1, f.getParams().size());
		assertParam(f, "param1");
		assertEquals(0, f.getVariables().size());

		assertEquals(p.body.size(), f.getBody().size());
		for (int i = 0; i < f.getBody().size(); i++) {
			assertEquals(p.body.get(i).toString(), f.getBody().get(i).toString());
		}

		param = new PVarDecl();
		param.var = "param2";
		p.params.add(param);
		f = PGoFunction.convert(p);
		assertEquals(p.name, f.getName());
		assertEquals(PGoFunction.FunctionType.Normal, f.getType());
		assertEquals(2, f.getParams().size());
		assertParam(f, "param1");
		assertEquals(0, f.getVariables().size());

		assertEquals(p.body.size(), f.getBody().size());
		for (int i = 0; i < f.getBody().size(); i++) {
			assertEquals(p.body.get(i).toString(), f.getBody().get(i).toString());
		}

		PVarDecl decl = new PVarDecl();
		decl.var = "var1";
		decl.val = PcalParams.DefaultVarInit();
		p.decls.add(decl);
		f = PGoFunction.convert(p);
		assertEquals(p.name, f.getName());
		assertEquals(PGoFunction.FunctionType.Normal, f.getType());
		assertEquals(2, f.getParams().size());
		assertParam(f, "param1", 0);
		assertParam(f, "param2", 1);
		assertEquals(1, f.getVariables().size());
		PGoVariable pdecl = f.getVariable("var1");
		assertNotNull(pdecl);
		assertEquals(decl.var, pdecl.getName());
		assertTrue(pdecl.getIsSimpleAssignInit());
		assertEquals(decl.val.toString(), pdecl.getPcalInitBlock().toString());

		assertEquals(p.body.size(), f.getBody().size());
		for (int i = 0; i < f.getBody().size(); i++) {
			assertEquals(p.body.get(i).toString(), f.getBody().get(i).toString());
		}

		LabeledStmt stmt = new LabeledStmt();
		stmt.label = "lab";
		stmt.stmts = new Vector<AST>();
		stmt.stmts.add(new Skip());

		p.body.add(stmt);
		f = PGoFunction.convert(p);
		assertEquals(p.name, f.getName());
		assertEquals(PGoFunction.FunctionType.Normal, f.getType());
		assertEquals(2, f.getParams().size());
		assertParam(f, "param1", 0);
		assertParam(f, "param2", 1);
		assertEquals(1, f.getVariables().size());
		pdecl = f.getVariable("var1");
		assertNotNull(pdecl);
		assertEquals(decl.var, pdecl.getName());
		assertTrue(pdecl.getIsSimpleAssignInit());
		assertEquals(decl.val.toString(), pdecl.getPcalInitBlock().toString());

		assertEquals(p.body.size(), f.getBody().size());
		for (int i = 0; i < f.getBody().size(); i++) {
			assertEquals(p.body.get(i).toString(), f.getBody().get(i).toString());
		}
	}

	@Test
	public void testConvertMacro() {
		Macro m = new Macro();
		m.name = "macroFunc";
		m.params = new Vector<String>();
		m.params.add("param1");

		m.body = new Vector<AST>();
		m.body.add(new Skip());
		
		PGoFunction f = PGoFunction.convert(m);
		assertEquals(m.name, f.getName());
		assertEquals(PGoFunction.FunctionType.Macro, f.getType());
		assertEquals(1, f.getParams().size());
		assertParam(f, "param1");

		assertEquals(m.body.size(), f.getBody().size());
		for (int i = 0; i < f.getBody().size(); i++) {
			assertEquals(m.body.get(i).toString(), f.getBody().get(i).toString());
		}

		m.name = "another";
		f = PGoFunction.convert(m);
		assertEquals(m.name, f.getName());
		assertEquals(PGoFunction.FunctionType.Macro, f.getType());
		assertEquals(1, f.getParams().size());
		assertParam(f, "param1");

		assertEquals(m.body.size(), f.getBody().size());
		for (int i = 0; i < f.getBody().size(); i++) {
			assertEquals(m.body.get(i).toString(), f.getBody().get(i).toString());
		}

		m.params.add("param2");
		f = PGoFunction.convert(m);
		assertEquals(m.name, f.getName());
		assertEquals(PGoFunction.FunctionType.Macro, f.getType());
		assertEquals(2, f.getParams().size());
		assertParam(f, "param1", 0);
		assertParam(f, "param2", 1);

		assertEquals(m.body.size(), f.getBody().size());
		for (int i = 0; i < f.getBody().size(); i++) {
			assertEquals(m.body.get(i).toString(), f.getBody().get(i).toString());
		}

		PrintS stmt = new PrintS();
		stmt.exp = PcalParams.DefaultVarInit();
		m.body.add(stmt);
		f = PGoFunction.convert(m);
		assertEquals(m.name, f.getName());
		assertEquals(PGoFunction.FunctionType.Macro, f.getType());
		assertEquals(2, f.getParams().size());
		assertParam(f, "param1", 0);
		assertParam(f, "param2", 1);

		assertEquals(m.body.size(), f.getBody().size());
		for (int i = 0; i < f.getBody().size(); i++) {
			assertEquals(m.body.get(i).toString(), f.getBody().get(i).toString());
		}
	}

	@Test
	public void testConvertProcess() {
		Process p = new Process();
		p.name = "client";
		p.decls = new Vector();
		p.body = new Vector<AST>();
		p.body.add(new Skip());

		PGoFunction f = PGoFunction.convert(p);
		assertEquals(p.name, f.getName());
		assertEquals(PGoFunction.FunctionType.GoRoutine, f.getType());
		assertEquals(1, f.getParams().size());
		assertParam(f, "self");

		assertEquals(p.body.size(), f.getBody().size());
		for (int i = 0; i < f.getBody().size(); i++) {
			assertEquals(p.body.get(i).toString(), f.getBody().get(i).toString());
		}
	}

	// Asserts correctness of parameter var in function f.
	// Asserts the existence, and that the variable name is correct.
	// The simple assignment should be true for functions, and the init block
	// null
	private void assertParam(PGoFunction f, String var) {
		PGoVariable param;
		param = f.getParam(var);
		assertNotNull(param);
		assertEquals(var, param.getName());
		assertTrue(param.getIsSimpleAssignInit());
		assertEquals(PcalParams.DefaultVarInit().toString(), param.getPcalInitBlock().toString());
	}

	// same as above, but asserts order of var
	private void assertParam(PGoFunction f, String var, int order) {
		assertEquals(var, f.getParams().get(order).getName());
		PGoVariable param;
		param = f.getParam(var);
		assertNotNull(param);
		assertEquals(var, param.getName());
		assertTrue(param.getIsSimpleAssignInit());
		assertEquals(PcalParams.DefaultVarInit().toString(), param.getPcalInitBlock().toString());
	}
}
