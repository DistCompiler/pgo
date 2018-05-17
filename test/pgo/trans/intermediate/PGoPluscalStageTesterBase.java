package pgo.trans.intermediate;

import java.util.ArrayList;

import pcal.AST;
import pgo.PGoPluscalTesterBase;
import pgo.model.intermediate.PGoFunction;
import pgo.model.type.PGoType;
import pgo.parser.PGoParseException;

/**
 * Abstract class for testing data of real pluscal algorithms for stage one
 * testing. This class will store the data of the pluscal algorithms such as the
 * variables, and functions so that we can assert our translated models with the
 * actual program.
 *
 */
public abstract class PGoPluscalStageTesterBase extends PGoPluscalTesterBase {

	public AST getAST() throws PGoParseException {
		return getParsedPcal().getAST();
	}

	// whether this pluscal algorithm is multiprocess
	public abstract boolean isMultiProcess();
	
	// the name of the algorithm
	public abstract String getName();

	// the variables and their data of the algorithm for various stages
	public abstract ArrayList<TestVariableData> getStageOneVariables();

	public ArrayList<TestVariableData> getStageTypeVariables() {
		return getStageOneVariables(); // in most cases we get by with the data
										// unchanged
	}

	// the functions of the algorithm for various stages
	public abstract ArrayList<TestFunctionData> getStageOneFunctions() throws PGoParseException;

	public ArrayList<TestFunctionData> getStageTypeFunctions() throws PGoParseException {
		return getStageOneFunctions(); // in most cases we can get by with the data unchanged.
	}

	public abstract int getNumGoroutineInit();

	// model storing data of each variable in the algorith
	public class TestVariableData {
		// variable name
		public final String name;
		// whether this has a simple initialization
		public final boolean isSimpleInit;
		// the tla string that initializes this variable
		public final String initBlock;
		// the go string that initializes this variable
		public final String goVal;
		// whether the variable is a constant
		public final boolean isConst;
		// the type of the var
		public final PGoType type;
		// whether this is a positional argument
		public final boolean isPositionalArg;
		// the argument flag name if applicable
		public String argFlag;
		// whether the variable needs to be atomic/thread safe
		public final boolean atomicity;

		public TestVariableData(String n, boolean isSimple, String init, String gv, boolean isconst, PGoType t,
				boolean isPos, String aflag, boolean isAtomic) {
			name = n;
			isSimpleInit = isSimple;
			initBlock = init;
			goVal = gv;
			isConst = isconst;
			type = t;
			isPositionalArg = isPos;
			argFlag = aflag;
			atomicity = isAtomic;
		}
	}

	// model storing data of each function in the algorithm
	public class TestFunctionData {
		// variable name
		public final String name;

		// The parameters to the function
		public final ArrayList<TestVariableData> params;

		// The declared variables of the function
		public final ArrayList<TestVariableData> vars;

		// The body of the function string form
		public final String body;

		// The type of the function
		public final PGoFunction.FunctionKind type;

		// The below is only present if its a goroutine
		// Whether the goroutine id is a simple initialization (just an assign)
		public final boolean isGoSimpleInit;
		// The string form of tlaexpr initializing the goroutine
		public final String goroutineInit;

		public final PGoType retType;

		public TestFunctionData(String n, ArrayList<TestVariableData> p, ArrayList<TestVariableData> v, String b,
								PGoFunction.FunctionKind ftype, boolean isSimple, String init, PGoType rType) {
			name = n;
			params = p;
			vars = v;
			body = b;
			type = ftype;
			isGoSimpleInit = isSimple;
			goroutineInit = init;
			retType = rType;
		}
	}
}
