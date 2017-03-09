package pgo;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.junit.BeforeClass;

import pcal.AST;
import pgo.pcalparser.PcalParser;

/**
 * Base test class for all tests requiring the pluscal algorithm files
 *
 */
public class PcalASTBase {
	protected static HashMap<String, AST> ast;
	protected static List<String> pcalAlgs;

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
}
