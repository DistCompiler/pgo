package pgo.trans.intermediate;

import java.util.ArrayList;

import pgo.trans.PGoPluscalTesterBase;

/**
 * Tester class for the FastMutex pluscal algorithm
 * 
 * This class stores the variables, functions and other data of the pluscal
 * algorithm to be used for validating the parsed and translated version of the
 * algorithm with the actual data.
 *
 */
public class FastMutexTester extends PGoPluscalTesterBase {

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
	public ArrayList<TestFunctionData> getFunctions() {
		return new ArrayList<TestFunctionData>();
	}

}
