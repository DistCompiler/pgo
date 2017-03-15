package pgo.trans.intermediate;

import java.util.ArrayList;

import pgo.trans.PGoPluscalTesterBase;

/**
 * Tester class for the QueensPluscal pluscal algorithm
 * 
 * This class stores the variables, functions and other data of the pluscal
 * algorithm to be used for validating the parsed and translated version of the
 * algorithm with the actual data.
 *
 */
public class QueensPluscalTester extends PGoPluscalTesterBase {

	@Override
	public boolean isMultiProcess() {
		return false;
	}

	public String getName() {
		return "QueensPluscal";
	}

	@Override
	public ArrayList<TestVariableData> getVariables() {
		ArrayList<TestVariableData> ret = new ArrayList<TestVariableData>();
		ret.add(new TestVariableData("todo", true, "<< \"{\", \"<<\", \">>\", \"}\" >>"));
		ret.add(new TestVariableData("sols", true, "<< \"{\", \"}\" >>"));

		return ret;
	}

	@Override
	public ArrayList<TestFunctionData> getFunctions() {
		return new ArrayList<TestFunctionData>();
	}
}
