package pgo;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.junit.BeforeClass;
import org.junit.runners.Parameterized;

import pcal.AST;
import pgo.pcalparser.PcalParser;
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

	protected String alg;
	protected PGoPluscalTesterBase tester;

	public PcalASTBase(String alg, PGoPluscalTesterBase tester) {
		this.alg = alg;
		this.tester = tester;
	}

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
		Logger.getLogger("PGoTrans AST Stage").setLevel(Level.INFO);
		pcalAlgs = Arrays.asList("Euclid", "Sum", "TwoPhaseCommit", "FastMutex", "QueensPluscal",
				"QueensPluscalProcedure");
		ast = new HashMap<String, AST>();
		for (String alg : pcalAlgs) {
			System.out.println(alg);
			AST a = new PcalParser("./test/pluscal/" + alg + ".tla").parse();

			ast.put(alg, a);
		}
	}

	@Parameterized.Parameters
	public static Collection primeNumbers() {
		return Arrays.asList(new Object[][] { { "Euclid", new EuclidTester() }, { "FastMutex", new FastMutexTester() },
				{ "QueensPluscal", new QueensPluscalTester() },
				{ "QueensPluscalProcedure", new QueensPluscalProcedureTester() },
				{ "Sum", new SumTester() }, { "TwoPhaseCommit", new TwoPhaseCommitTester() } });
	}
}
