package pgo;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;

import org.junit.runners.Parameterized;

import pcal.AST;
import pgo.trans.PGoPluscalTesterBase;
import pgo.trans.intermediate.EuclidTester;
import pgo.trans.intermediate.FastMutexTester;
import pgo.trans.intermediate.QueensPluscalProcedureTester;
import pgo.trans.intermediate.QueensPluscalTester;
import pgo.trans.intermediate.SumTester;
import pgo.trans.intermediate.TwoPhaseCommitTester;

/**
 * Base test class for all tests requiring the pluscal algorithm files
 *
 */
public class PcalASTBase {
	protected static HashMap<String, AST> ast;
	protected static List<String> pcalAlgs;

	protected PGoPluscalTesterBase tester;

	public PcalASTBase(PGoPluscalTesterBase tester) {
		this.tester = tester;
	}

	@Parameterized.Parameters
	public static Collection primeNumbers() {
		return Arrays.asList(
				new Object[][] { { new EuclidTester() }, { new FastMutexTester() }, { new QueensPluscalTester() },
						{ new QueensPluscalProcedureTester() }, { new SumTester() }, { new TwoPhaseCommitTester() } });
	}
}
