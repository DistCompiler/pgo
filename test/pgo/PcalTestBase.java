package pgo;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;

import org.junit.runners.Parameterized;

import pcal.AST;
import pgo.trans.intermediate.EuclidIntermediateTester;
import pgo.trans.intermediate.FastMutexIntermediateTester;
import pgo.trans.intermediate.PGoPluscalStageOneTesterBase;
import pgo.trans.intermediate.QueensPluscalProcedureIntermediateTester;
import pgo.trans.intermediate.QueensPluscalIntermediateTester;
import pgo.trans.intermediate.SumIntermediateTester;
import pgo.trans.intermediate.TwoPhaseCommitIntermediateTester;

/**
 * Base test class for all tests requiring the pluscal algorithm files
 *
 */
public class PcalTestBase {
	protected static HashMap<String, AST> ast;
	protected static List<String> pcalAlgs;

	protected PGoPluscalStageOneTesterBase tester;

	public PcalTestBase(PGoPluscalStageOneTesterBase tester) {
		this.tester = tester;
	}

	@Parameterized.Parameters
	public static Collection primeNumbers() {
		return Arrays.asList(
				new Object[][] { { new EuclidIntermediateTester() }, { new FastMutexIntermediateTester() }, { new QueensPluscalIntermediateTester() },
						{ new QueensPluscalProcedureIntermediateTester() }, { new SumIntermediateTester() }, { new TwoPhaseCommitIntermediateTester() } });
	}
}
