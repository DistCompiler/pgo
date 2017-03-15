package pgo.trans.intermediate;

import java.util.ArrayList;

import pgo.trans.PGoPluscalTesterBase;

/**
 * Tester class for the Sum pluscal algorithm
 * 
 * This class stores the variables, functions and other data of the pluscal
 * algorithm to be used for validating the parsed and translated version of the
 * algorithm with the actual data.
 *
 */
public class SumTester extends PGoPluscalTesterBase {

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
	public ArrayList<TestFunctionData> getFunctions() {
		ArrayList<TestFunctionData> ret = new ArrayList<TestFunctionData>();

		ArrayList<TestVariableData> params = new ArrayList<TestVariableData>();
		ArrayList<TestVariableData> vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("from", true, "<< \"defaultInitValue\" >>"));
		params.add(new TestVariableData("to", true, "<< \"defaultInitValue\" >>"));
		params.add(new TestVariableData("msg", true, "<< \"defaultInitValue\" >>"));

		String b = "[[type |-> \"assignment\",\n "
				+ "ass  |-> <<[lhs |-> [var |-> \"network\", sub |-> << \"[\", \"to\", \"]\" >>],\n"
				+ "             rhs |-> << \"Append\", \"(\","
				+ " \"network\", \"[\", \"to\", \"]\", \",\", \"<<\", \"from\", \",\","
				+ " \"msg\", \">>\", \")\" >>]>>]]";

		ret.add(new TestFunctionData("SendTo", params, vars, b));

		params = new ArrayList<TestVariableData>();
		vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("to", true, "<< \"defaultInitValue\" >>"));
		params.add(new TestVariableData("id", true, "<< \"defaultInitValue\" >>"));
		params.add(new TestVariableData("msg", true, "<< \"defaultInitValue\" >>"));

		b = "[[type |-> \"when\", \n exp |-> << \"network\", \"[\","
				+ " \"to\", \"]\", \"#\", \"<<\", \">>\" >>], [type |-> \"assignment\",\n "
				+ "ass  |-> <<[lhs |-> [var |-> \"id\", sub |-> <<  >>],\n             "
				+ "rhs |-> << \"Head\", \"(\", \"network\", \"[\", \"to\", \"]\", \")\", "
				+ "\"[\", \"1\", \"]\" >>]>>], [type |-> \"assignment\",\n"
				+ " ass  |-> <<[lhs |-> [var |-> \"msg\", sub |-> <<  >>],\n"
				+ "             rhs |-> << \"Head\", \"(\", \"network\", "
				+ "\"[\", \"to\", \"]\", \")\", \"[\", \"2\", \"]\" >>]>>], "
				+ "[type |-> \"assignment\",\n ass  |-> <<[lhs |-> "
				+ "[var |-> \"network\", sub |-> << \"[\", \"to\", \"]\" >>],\n"
				+ "             rhs |-> << \"Tail\", \"(\", \"network\", "
				+ "\"[\", \"to\", \"]\", \")\" >>]>>]]";

		ret.add(new TestFunctionData("Recv", params, vars, b));
		return ret;
	}
}
