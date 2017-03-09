package pgo.trans.intermediate;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;

import pcal.AST;
import pgo.PcalASTBase;
import pgo.trans.PGoTransException;
import pgo.trans.intermediate.model.PGoVariable;

public class PGoTransStageOneTest extends PcalASTBase {

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
		
		for (String alg : Arrays.asList("Sum", "TwoPhaseCommit", "FastMutex")) {
			PGoTransStageOne p = new PGoTransStageOne(ast.get(alg));
			assertTrue(p.getIsMultiProcess());
		}
		for (String alg : Arrays.asList("Euclid", "QueensPluscal", "QueensPluscalProcedure")) {
			PGoTransStageOne p = new PGoTransStageOne(ast.get(alg));
			assertFalse(p.getIsMultiProcess());
		}
	}

	@Test
	public void testAlgName() throws PGoTransException {
		for (String alg : pcalAlgs) {
			PGoTransStageOne p = new PGoTransStageOne(ast.get(alg));
			assertEquals(alg, p.getAlgName());
		}
	}

	// assert function for a pgovariable generated from initial pass
	protected void assertPGoVariable(PGoTransStageOne p, String varName, boolean isSimpleAssignInit, String initBlock) {
		PGoVariable v = p.getGlobal(varName);
		assertNotNull(v);
		assertEquals(varName, v.getName());
		assertEquals(isSimpleAssignInit, v.getIsSimpleAssignInit());
		assertEquals(initBlock, v.getPcalInitBlock().toString());
	}

	@Test
	public void testVarFromEuclid() throws PGoTransException {
		PGoTransStageOne p = new PGoTransStageOne(ast.get("Euclid"));
		Collection<PGoVariable> cv = p.getGlobals();

		assertEquals(3, cv.size());

		assertPGoVariable(p, "u", true, "<< \"24\" >>");
		assertPGoVariable(p, "v", false, "<< \"1\", \"..\", \"N\" >>");
		assertPGoVariable(p, "v_init", true, "<< \"v\" >>");
	}

	@Test
	public void testVarFromQueensPluscal() throws PGoTransException {
		PGoTransStageOne p = new PGoTransStageOne(ast.get("QueensPluscal"));
		Collection<PGoVariable> cv = p.getGlobals();

		assertEquals(cv.size(), 2);

		assertPGoVariable(p, "todo", true, "<< \"{\", \"<<\", \">>\", \"}\" >>");
		assertPGoVariable(p, "sols", true, "<< \"{\", \"}\" >>");
	}

	@Test
	public void testVarFromQueensPluscalProcedure() throws PGoTransException {
		PGoTransStageOne p = new PGoTransStageOne(ast.get("QueensPluscalProcedure"));
		Collection<PGoVariable> cv = p.getGlobals();

		assertEquals(3, cv.size());

		assertPGoVariable(p, "todo", true, "<< \"{\", \"<<\", \">>\", \"}\" >>");
		assertPGoVariable(p, "sols", true, "<< \"{\", \"}\" >>");
		assertPGoVariable(p, "rVal", true, "<< \"defaultInitValue\" >>");
	}

	@Test
	public void testVarFromSum() throws PGoTransException {
		PGoTransStageOne p = new PGoTransStageOne(ast.get("Sum"));
		Collection<PGoVariable> cv = p.getGlobals();

		assertEquals(cv.size(), 1);

		assertPGoVariable(p, "network", true,
				"<< \"[\", \"i\", \"\\\\in\", \"1\", \"..\", \"N\", \"+\", \"1\","
						+ " \"|->\", \"<<\", \">>\", \"]\" >>");
	}

	@Test
	public void testVarFromTwoPhaseCommit() throws PGoTransException {
		PGoTransStageOne p = new PGoTransStageOne(ast.get("TwoPhaseCommit"));
		Collection<PGoVariable> cv = p.getGlobals();

		assertEquals(2, cv.size());

		assertPGoVariable(p, "managers", true,"<< \"{\", \"\\\"\", \"bob\", \"\\\"\","
				+ " \",\", \"\\\"\", \"chuck\", \"\\\"\", \",\", \"\\\"\", \"dave\", "
				+ "\"\\\"\", \",\", \"\\\"\", \"everett\", \"\\\"\", \",\", \"\\\"\","
				+ " \"fred\", \"\\\"\", \"}\" >>");
				
		assertPGoVariable(p, "restaurant_stage", true,
				"<< \"[\", \"mgr\", \"\\\\in\", \"managers\", \"|->\", \"\\\"\", \"start\", \"\\\"\", \"]\" >>");
	}

	@Test
	public void testVarFromFastMutex() throws PGoTransException {
		PGoTransStageOne p = new PGoTransStageOne(ast.get("FastMutex"));
		Collection<PGoVariable> cv = p.getGlobals();

		assertEquals(3, cv.size());

		assertPGoVariable(p, "x", true, "<< \"defaultInitValue\" >>");
		assertPGoVariable(p, "y", true, "<< \"0\" >>");
		assertPGoVariable(p, "b", true,
				"<< \"[\", \"i\", \"\\\\in\", \"1\", \"..\", \"N\", \"|->\", \"FALSE\", \"]\" >>");
	}

}
