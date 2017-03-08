package pgo.trans.intermediate;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.Arrays;

import org.junit.Test;

import pcal.AST;
import pgo.PcalASTBase;
import pgo.trans.PGoTransException;

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
		for (String alg : Arrays.asList("Euclid")) {
			PGoTransStageOne p = new PGoTransStageOne(ast.get(alg));
			assertFalse(p.getIsMultiProcess());
		}
	}

}
