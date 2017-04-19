package pgo.trans.intermediate;

import java.util.ArrayList;

import pcal.AST.Multiprocess;
import pcal.AST.Process;
import pgo.model.intermediate.PGoFunction;
import pgo.parser.PGoParseException;

/**
 * Tester class for the FastMutex pluscal algorithm
 * 
 * This class stores the variables, functions and other data of the pluscal
 * algorithm to be used for validating the parsed and translated version of the
 * algorithm with the actual data.
 *
 */
public class FastMutexIntermediateTester extends PGoPluscalStageOneTesterBase {

	@Override
	public boolean isMultiProcess() {
		return true;
	}

	public String getName() {
		return "FastMutex";
	}

	@Override
	public ArrayList<TestVariableData> getVariables() {
		ArrayList<TestVariableData> ret = new ArrayList<TestVariableData>();
		ret.add(new TestVariableData("x", true, "<< \"defaultInitValue\" >>"));
		ret.add(new TestVariableData("y", true, "<< \"0\" >>"));
		ret.add(new TestVariableData("b", true,
				"<< \"[\", \"i\", \"\\\\in\", \"1\", \"..\", \"N\", \"|->\", \"FALSE\", \"]\" >>"));
		return ret;
	}

	@Override
	public ArrayList<TestFunctionData> getFunctions() throws PGoParseException {
		ArrayList<TestFunctionData> r = new ArrayList<TestFunctionData>();

		ArrayList<TestVariableData> params = new ArrayList<TestVariableData>();
		ArrayList<TestVariableData> vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("self", true, "<< \"defaultInitValue\" >>"));
		vars.add(new TestVariableData("j", true, "<< \"defaultInitValue\" >>"));

		String b = ((Process) ((Multiprocess) getAST()).procs.get(0)).body.toString();

		r.add(new TestFunctionData("Proc", params, vars, b, PGoFunction.FunctionType.GoRoutine, false,
				"<< \"1\", \"..\", \"N\" >>"));

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
