package pgo.trans;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.logging.Level;
import java.util.logging.Logger;

import pcal.AST;
import pgo.pcalparser.PcalParseException;
import pgo.pcalparser.PcalParser;

/**
 * Abstract class for testing data of real pluscal algorithms.
 * This class will store the data of the pluscal algorithms such as the variables, and functions so that we can assert our translated models with the actual program.
 *
 */
public abstract class PGoPluscalTesterBase {
	private static HashMap<String, AST> ast = new HashMap<String, AST>();

	// Gets the AST of this pluscal algorithm
	public AST getAST() throws PcalParseException {
		AST r = ast.get(getAlg());
		if (r != null) {
			return r;
		}
		Logger.getLogger("PGoTrans AST Stage").setLevel(Level.INFO);
		r = new PcalParser("./test/pluscal/" + getAlg() + ".tla").parse();
		ast.put(getAlg(), r);
		return r;
	}

	protected abstract String getAlg();

	// whether this pluscal algorithm is multiprocess
	public abstract boolean isMultiProcess();
	
	// the name of the algorithm
	public abstract String getName();

	// the variables and their data of the algorithm
	public abstract ArrayList<TestVariableData> getVariables();

	// the functions of the algorithm
	public abstract ArrayList<TestFunctionData> getFunctions() throws PcalParseException;

	public abstract int getNumGoroutineInit();

	// model storing data of each variable in the algorith
	public class TestVariableData {
		// variable name
		public final String name;
		// whether this has a simple initialization
		public final boolean isSimpleInit;
		// the tla string that initializes this variable
		public final String initBlock;

		public TestVariableData(String n, boolean isSimple, String init) {
			name = n;
			isSimpleInit = isSimple;
			initBlock = init;
		}
	}

	// model storing data of each function in the algorith
	public class TestFunctionData {
		// variable name
		public final String name;

		// The parameters to the function
		public final ArrayList<TestVariableData> params;

		// The declared variables of the function
		public final ArrayList<TestVariableData> vars;

		// The body of the function string form
		public final String body;

		// Whether this function came from goroutine
		public final boolean isGoRoutine;

		// The below is only present if its a goroutine
		// Whether the goroutine id is a simple initialization (just an assign)
		public final boolean isGoSimpleInit;
		// The string form of tlaexpr initializing the goroutine
		public final String goroutineInit;

		public TestFunctionData(String n, ArrayList<TestVariableData> p, ArrayList<TestVariableData> v, String b,
				boolean goroutine, boolean isSimple, String init) {
			name = n;
			params = p;
			vars = v;
			body = b;
			isGoRoutine = goroutine;
			isGoSimpleInit = isSimple;
			goroutineInit = init;
		}
	}

}
