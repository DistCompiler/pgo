package pgo.trans.intermediate;

import java.util.ArrayList;

import pgo.trans.PGoPluscalTesterBase;

/**
 * Tester class for the TwoPhaseCommit pluscal algorithm
 * 
 * This class stores the variables, functions and other data of the pluscal
 * algorithm to be used for validating the parsed and translated version of the
 * algorithm with the actual data.
 *
 */
public class TwoPhaseCommitTester extends PGoPluscalTesterBase {

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
	public ArrayList<TestFunctionData> getFunctions() {
		ArrayList<TestFunctionData> ret = new ArrayList<TestFunctionData>();

		ArrayList<TestVariableData> params = new ArrayList<TestVariableData>();
		ArrayList<TestVariableData> vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("state", true, "<< \"defaultInitValue\" >>"));
		params.add(new TestVariableData("kmgrs", true, "<< \"defaultInitValue\" >>"));

		String b = "[[type    |-> \"while\", \n test    |-> << \"kmgrs\", \"#\", \"{\", \"}\" >>,\n "
				+ "labDo   |-> <<>>,\n unlabDo |-> <<[type   |-> \"with\", \n                "
				+ "var    |-> \"km\",\n                eqOrIn |-> \"\\\\in\",\n                "
				+ "exp    |-> << \"kmgrs\" >>,\n                do     |-> <<[type |-> "
				+ "\"assignment\",\n                              ass  |-> <<[lhs |-> "
				+ "[var |-> \"restaurant_stage\", sub |-> << \"[\", \"km\", \"]\" >>],\n"
				+ "                                          rhs |-> << \"state\" >>]>>], \n"
				+ "                             [type |-> \"assignment\",\n"
				+ "                              ass  |-> <<[lhs |-> [var |-> \"kmgrs\", sub |-> <<  >>],\n"
				+ "                                          rhs |-> << \"kmgrs\", \"\\\\\", \"{\", \"km\", \"}\" >>]>>]>>]>>]]";

		ret.add(new TestFunctionData("SetAll", params, vars, b));

		return ret;
	}

}
