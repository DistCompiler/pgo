package pgo.trans.intermediate;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.fail;

import java.util.ArrayList;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import pcal.AST;
import pgo.PcalASTBase;
import pgo.trans.PGoPluscalTesterBase;
import pgo.trans.PGoPluscalTesterBase.TestFunctionData;
import pgo.trans.PGoPluscalTesterBase.TestVariableData;
import pgo.trans.PGoTransException;
import pgo.trans.intermediate.model.PGoFunction;
import pgo.trans.intermediate.model.PGoVariable;

@RunWith(Parameterized.class)
public class PGoTransStageOneTest extends PcalASTBase {

	public PGoTransStageOneTest(String alg, PGoPluscalTesterBase tester) {
		super(alg, tester);
	}


	@Test
	public void testUniOrMultiProcess() throws PGoTransException {
		boolean succ = false;
		try {
			PGoTransStageOne p = new PGoTransStageOne(new AST());
		} catch (PGoTransException e) {
			// success
			succ = true;
		}
		if (!succ) {
			fail("Expected PGoTransException from parsing");
		}
		
		PGoTransStageOne p = new PGoTransStageOne(ast.get(alg));
		assertEquals(tester.isMultiProcess(), p.getIsMultiProcess());
	}

	@Test
	public void testAlgName() throws PGoTransException {
		PGoTransStageOne p = new PGoTransStageOne(ast.get(alg));
		assertEquals(tester.getName(), p.getAlgName());

	}

	@Test
	public void testPGoVariable() throws PGoTransException {
		PGoTransStageOne p = new PGoTransStageOne(ast.get(alg));
		ArrayList<PGoVariable> cv = p.getGlobals();
		assertEquals(tester.getVariables().size(), cv.size());

		for (int i = 0; i < cv.size(); i++) {
			assertPGoVariable(p.getGlobals().get(i), i, tester.getVariables());
			assertEquals(p.getGlobals().get(i), p.getGlobal(p.getGlobals().get(i).getName()));
		}
	}

	// assert function for a pgovariable generated from initial pass
	private void assertPGoVariable(PGoVariable v, int i, ArrayList<TestVariableData> tv) {
		TestVariableData av = tv.get(i);

		assertNotNull(v);
		assertEquals(av.name, v.getName());
		assertEquals(av.isSimpleInit, v.getIsSimpleAssignInit());
		assertEquals(av.initBlock, v.getPcalInitBlock().toString());
	}

	@Test
	public void testPGoFunction() throws PGoTransException {
		PGoTransStageOne p = new PGoTransStageOne(ast.get(alg));

		ArrayList<PGoFunction> cv = p.getFunctions();
		assertEquals(tester.getFunctions().size(), cv.size());

		for (int i = 0; i < cv.size(); i++) {
			assertPGoFunction(p, i, tester);
		}
	}

	// assert function for a pgofunction generated from initial pass
	private void assertPGoFunction(PGoTransStageOne p, int i, PGoPluscalTesterBase tester) {
		TestFunctionData af = tester.getFunctions().get(i);

		PGoFunction f = p.getFunctions().get(i);
		assertNotNull(f);
		assertEquals(af.name, f.getName());
		assertEquals(af.body, f.getBody().toString());

		assertEquals(af.params.size(), f.getParams().size());
		for (int j = 0; j < f.getParams().size(); j++) {
			assertPGoVariable(f.getParams().get(j), j, af.params);
			assertEquals(f.getParams().get(j), f.getParam(f.getParams().get(j).getName()));
		}
		
		assertEquals(af.vars.size(), f.getVariables().size());
		for (int j = 0; j < f.getVariables().size(); j++) {
			assertPGoVariable(f.getVariables().get(j), j, af.params);
			assertEquals(f.getVariables().get(j), f.getVariable(f.getVariables().get(j).getName()));
		}

		assertEquals(p.getFunction(af.name), f);
	}
}
