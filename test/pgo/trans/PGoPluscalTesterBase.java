package pgo.trans;

import java.util.ArrayList;

/**
 * Abstract class for testing data of real pluscal algorithms.
 * This class will store the data of the pluscal algorithms such as the variables, and functions so that we can assert our translated models with the actual program.
 *
 */
public abstract class PGoPluscalTesterBase {
	// whether this pluscal algorithm is multiprocess
	public abstract boolean isMultiProcess();
	
	// the name of the algorithm
	public abstract String getName();

	// the variables and their data of the algorithm
	public abstract ArrayList<TestVariableData> getVariables();

	// the functions of the algorithm
	public abstract ArrayList<TestFunctionData> getFunctions();

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

		public TestFunctionData(String n, ArrayList<TestVariableData> p, ArrayList<TestVariableData> v, String b) {
			name = n;
			params = p;
			vars = v;
			body = b;
		}
	}

}
