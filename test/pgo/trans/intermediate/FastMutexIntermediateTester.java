package pgo.trans.intermediate;

import java.util.ArrayList;

import pcal.AST.Multiprocess;
import pcal.AST.Process;
import pgo.model.intermediate.PGoCollectionType;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoType;
import pgo.parser.PGoParseException;

/**
 * Tester class for the FastMutex pluscal algorithm
 * 
 * This class stores the variables, functions and other data of the pluscal
 * algorithm to be used for validating the parsed and translated version of the
 * algorithm with the actual data.
 *
 */
public class FastMutexIntermediateTester extends PGoPluscalStageTesterBase {

	@Override
	public boolean isMultiProcess() {
		return true;
	}

	public String getName() {
		return "FastMutex";
	}

	@Override
	public ArrayList<TestVariableData> getStageOneVariables() {
		ArrayList<TestVariableData> ret = new ArrayList<TestVariableData>();
		ret.add(new TestVariableData("x", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(),
				false, "", true));
		ret.add(new TestVariableData("y", true, "<< \"0\" >>", "", false, new PGoPrimitiveType.PGoNatural(), false,
				"", true));
		ret.add(new TestVariableData("b", true,
				"<< \"[\", \"i\", \"\\\\in\", \"1\", \"..\", \"N\", \"|->\", \"FALSE\", \"]\" >>", "", false,
				new PGoCollectionType.PGoSlice("bool"), false, "", true));
		return ret;
	}

	@Override
	public ArrayList<TestVariableData> getStageTypeVariables() {
		ArrayList<TestVariableData> ret = getStageOneVariables();
		ret.add(new TestVariableData("N", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, "numT", false));
		return ret;
	}

	@Override
	public ArrayList<TestFunctionData> getStageOneFunctions() throws PGoParseException {
		ArrayList<TestFunctionData> r = new ArrayList<TestFunctionData>();

		ArrayList<TestVariableData> params = new ArrayList<TestVariableData>();
		ArrayList<TestVariableData> vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("self", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, "", false));
		vars.add(new TestVariableData("j", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, "", false));

		String b = ((Process) ((Multiprocess) getAST()).procs.get(0)).body.toString();

		r.add(new TestFunctionData("Proc", params, vars, b, PGoFunction.FunctionType.GoRoutine, false,
				"<< \"1\", \"..\", \"N\" >>", PGoType.VOID));

		return r;
	}

	@Override
	public int getNumGoroutineInit() {
		return 1;
	}

	@Override
	protected String getAlg() {
		return "FastMutex";
	}

}
