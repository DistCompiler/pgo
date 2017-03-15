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
public class QueensPluscalProcedureTester extends PGoPluscalTesterBase {

	@Override
	public boolean isMultiProcess() {
		return false;
	}

	public String getName() {
		return "QueensPluscalProcedure";
	}

	@Override
	public ArrayList<TestVariableData> getVariables() {
		ArrayList<TestVariableData> ret = new ArrayList<TestVariableData>();
		ret.add(new TestVariableData("todo", true, "<< \"{\", \"<<\", \">>\", \"}\" >>"));
		ret.add(new TestVariableData("sols", true, "<< \"{\", \"}\" >>"));
		ret.add(new TestVariableData("rVal", true, "<< \"defaultInitValue\" >>"));

		return ret;
	}

	@Override
	public ArrayList<TestFunctionData> getFunctions() {
		ArrayList<TestFunctionData> ret = new ArrayList<TestFunctionData>();

		ArrayList<TestVariableData> params = new ArrayList<TestVariableData>();
		ArrayList<TestVariableData> vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("queens", true, "<< \"defaultInitValue\" >>"));
		params.add(new TestVariableData("i", true, "<< \"defaultInitValue\" >>"));
		params.add(new TestVariableData("j", true, "<< \"defaultInitValue\" >>"));

		String b = "[[label |-> \"attlabl\",\n stmts |-> <<[type |-> \"assignment\",\n              "
				+ "ass  |-> <<[lhs |-> [var |-> \"rVal\", sub |-> <<  >>],\n                          "
				+ "rhs |-> << \"\\\\/\", \"queens\", \"[\", \"i\", \"]\", \"=\", \"queens\", \"[\", \"j\", \"]\"\n, "
				+ "\"\\\\/\", \"queens\", \"[\", \"i\", \"]\", \"-\", \"queens\", \"[\", \"j\", \"]\", \"=\", \"i\", \"-\", \"j\"\n, "
				+ "\"\\\\/\", \"queens\", \"[\", \"j\", \"]\", \"-\", \"queens\", \"[\", \"i\", \"]\", \"=\", \"i\", \"-\", \"j\" >>]>>], \n"
				+ "             [type |-> \"return\", from |-> \"PgoAttacks\"]>>]]";

		ret.add(new TestFunctionData("PgoAttacks", params, vars, b));
		return ret;
	}

}
