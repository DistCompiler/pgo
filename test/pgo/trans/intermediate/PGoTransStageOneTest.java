package pgo.trans.intermediate;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
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
			assertEquals(p.getAlgName(), alg);
		}
	}

	@Test
	public void testVarFromEuclid() throws PGoTransException {
		PGoTransStageOne p = new PGoTransStageOne(ast.get("Euclid"));
		Collection<PGoVariable> cv = p.getGlobals();

		assertEquals(cv.size(), 3);

		PGoVariable[] var = cv.toArray(new PGoVariable[cv.size()]);

		PGoVariable u = var[0];
		assertEquals(u.getName(), "u");
		assertTrue(u.getIsSimpleAssignInit());
		assertEquals(u.getPcalInitBlock().toString(), "<< \"24\" >>");

		PGoVariable v = var[1];
		assertEquals(v.getName(), "v");
		assertFalse(v.getIsSimpleAssignInit());
		assertEquals(v.getPcalInitBlock().toString(), "<< \"1\", \"..\", \"N\" >>");

		PGoVariable v_init = var[2];
		assertEquals(v_init.getName(), "v_init");
		assertTrue(v_init.getIsSimpleAssignInit());
		assertEquals(v_init.getPcalInitBlock().toString(), "<< \"v\" >>");
	}

}
