package pgo.trans.intermediate;

import java.util.ArrayList;

import pcal.AST.Macro;
import pcal.AST.Multiprocess;
import pcal.AST.Process;
import pgo.parser.PGoParseException;

/**
 * Tester class for the Sum pluscal algorithm
 * 
 * This class stores the variables, functions and other data of the pluscal
 * algorithm to be used for validating the parsed and translated version of the
 * algorithm with the actual data.
 *
 */
public class SumIntermediateTester extends PGoPluscalStageOneTesterBase {

	@Override
	public boolean isMultiProcess() {
		return true;
	}

	public String getName() {
		return "Sum";
	}

	@Override
	public ArrayList<TestVariableData> getVariables() {
		ArrayList<TestVariableData> ret = new ArrayList<TestVariableData>();
		ret.add(new TestVariableData("network", true, "<< \"[\", \"i\", \"\\\\in\", "
				+ "\"1\", \"..\", \"N\", \"+\", \"1\", \"|->\", \"<<\", \">>\", \"]\" >>"));

		return ret;
	}

	@Override
	public ArrayList<TestFunctionData> getFunctions() throws PGoParseException {
		ArrayList<TestFunctionData> ret = new ArrayList<TestFunctionData>();

		ArrayList<TestVariableData> params = new ArrayList<TestVariableData>();
		ArrayList<TestVariableData> vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("from", true, "<< \"defaultInitValue\" >>"));
		params.add(new TestVariableData("to", true, "<< \"defaultInitValue\" >>"));
		params.add(new TestVariableData("msg", true, "<< \"defaultInitValue\" >>"));

		String b = ((Macro) ((Multiprocess) getAST()).macros.get(0)).body.toString();

		ret.add(new TestFunctionData("SendTo", params, vars, b, false, false, ""));

		params = new ArrayList<TestVariableData>();
		vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("to", true, "<< \"defaultInitValue\" >>"));
		params.add(new TestVariableData("id", true, "<< \"defaultInitValue\" >>"));
		params.add(new TestVariableData("msg", true, "<< \"defaultInitValue\" >>"));

		b = ((Macro) ((Multiprocess) getAST()).macros.get(1)).body.toString();

		ret.add(new TestFunctionData("Recv", params, vars, b, false, false, ""));

		params = new ArrayList<TestVariableData>();
		vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("self", true, "<< \"defaultInitValue\" >>"));
		vars.add(new TestVariableData("a_init", true, "<< \"defaultInitValue\" >>"));
		vars.add(new TestVariableData("b_init", true, "<< \"defaultInitValue\" >>"));
		vars.add(new TestVariableData("runs", true, "<< \"0\" >>"));
		vars.add(new TestVariableData("id", true, "<< \"defaultInitValue\" >>"));
		vars.add(new TestVariableData("msg", true, "<< \"defaultInitValue\" >>"));
		vars.add(new TestVariableData("sum", true, "<< \"defaultInitValue\" >>"));

		b = ((Process) ((Multiprocess) getAST()).procs.get(0)).body.toString();

		ret.add(new TestFunctionData("Client", params, vars, b, true, false, "<< \"1\", \"..\", \"N\" >>"));

		params = new ArrayList<TestVariableData>();
		vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("self", true, "<< \"defaultInitValue\" >>"));
		vars.add(new TestVariableData("a", true, "<< \"defaultInitValue\" >>"));
		vars.add(new TestVariableData("b", true, "<< \"defaultInitValue\" >>"));
		vars.add(new TestVariableData("id", true, "<< \"defaultInitValue\" >>"));
		vars.add(new TestVariableData("msg", true, "<< \"defaultInitValue\" >>"));

		b = ((Process) ((Multiprocess) getAST()).procs.get(1)).body.toString();

		ret.add(new TestFunctionData("Server", params, vars, b, true, true, "<< \"N\", \"+\", \"1\" >>"));

		return ret;
	}

	@Override
	protected String getAlg() {
		return "Sum";
	}

	@Override
	public int getNumGoroutineInit() {
		return 2;
	}
}
