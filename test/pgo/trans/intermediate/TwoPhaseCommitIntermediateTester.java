package pgo.trans.intermediate;

import java.util.ArrayList;

import pcal.AST.Macro;
import pcal.AST.Multiprocess;
import pcal.AST.Process;
import pgo.parser.PGoParseException;

/**
 * Tester class for the TwoPhaseCommit pluscal algorithm
 * 
 * This class stores the variables, functions and other data of the pluscal
 * algorithm to be used for validating the parsed and translated version of the
 * algorithm with the actual data.
 *
 */
public class TwoPhaseCommitIntermediateTester extends PGoPluscalStageOneTesterBase {

	@Override
	public boolean isMultiProcess() {
		return true;
	}

	public String getName() {
		return "TwoPhaseCommit";
	}

	@Override
	public ArrayList<TestVariableData> getVariables() {
		ArrayList<TestVariableData> ret = new ArrayList<TestVariableData>();
		ret.add(new TestVariableData("managers", true,"<< \"{\", \"\\\"\", \"bob\", \"\\\"\","
				+ " \",\", \"\\\"\", \"chuck\", \"\\\"\", \",\", \"\\\"\", \"dave\", "
				+ "\"\\\"\", \",\", \"\\\"\", \"everett\", \"\\\"\", \",\", \"\\\"\","
				+ " \"fred\", \"\\\"\", \"}\" >>"));
				
		ret.add(new TestVariableData("restaurant_stage", true,
				"<< \"[\", \"mgr\", \"\\\\in\", \"managers\", \"|->\", \"\\\"\", \"start\", \"\\\"\", \"]\" >>"));
		return ret;
	}

	@Override
	public ArrayList<TestFunctionData> getFunctions() throws PGoParseException {
		ArrayList<TestFunctionData> ret = new ArrayList<TestFunctionData>();

		ArrayList<TestVariableData> params = new ArrayList<TestVariableData>();
		ArrayList<TestVariableData> vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("state", true, "<< \"defaultInitValue\" >>"));
		params.add(new TestVariableData("kmgrs", true, "<< \"defaultInitValue\" >>"));

		String b = ((Macro) ((Multiprocess) getAST()).macros.get(0)).body.toString();

		ret.add(new TestFunctionData("SetAll", params, vars, b, false, false, ""));

		params = new ArrayList<TestVariableData>();
		vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("self", true, "<< \"defaultInitValue\" >>"));

		b = ((Process) ((Multiprocess) getAST()).procs.get(0)).body.toString();

		ret.add(new TestFunctionData("Restaurant", params, vars, b, true, false, "<< \"managers\" >>"));

		params = new ArrayList<TestVariableData>();
		vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("self", true, "<< \"defaultInitValue\" >>"));
		vars.add(new TestVariableData("rstMgrs", true, "<< \"defaultInitValue\" >>"));
		vars.add(new TestVariableData("aborted", true, "<< \"FALSE\" >>"));
		
		b = ((Process) ((Multiprocess) getAST()).procs.get(1)).body.toString();

		ret.add(new TestFunctionData("Controller", params, vars, b, true, true, "<< \"\\\"\", \"alice\", \"\\\"\" >>"));
		
		return ret;
	}

	@Override
	protected String getAlg() {
		return "TwoPhaseCommit";
	}

	@Override
	public int getNumGoroutineInit() {
		return 2;
	}

}
