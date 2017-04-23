package pgo.trans.intermediate;

import java.util.ArrayList;

import pgo.model.intermediate.PGoCollectionType;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoType;

/**
 * Tester class for the QueensPluscal pluscal algorithm
 * 
 * This class stores the variables, functions and other data of the pluscal
 * algorithm to be used for validating the parsed and translated version of the
 * algorithm with the actual data.
 *
 */
public class QueensPluscalProcedureIntermediateTester extends PGoPluscalStageTesterBase {

	@Override
	public boolean isMultiProcess() {
		return false;
	}

	public String getName() {
		return "QueensPluscalProcedure";
	}

	@Override
	public ArrayList<TestVariableData> getStageOneVariables() {
		ArrayList<TestVariableData> ret = new ArrayList<TestVariableData>();
		ret.add(new TestVariableData("todo", true, "<< \"{\", \"<<\", \">>\", \"}\" >>", "", false,
				new PGoCollectionType.PGoSet("chan[int]"), false, ""));
		ret.add(new TestVariableData("sols", true, "<< \"{\", \"}\" >>", "", false,
				new PGoCollectionType.PGoSet("chan[int]"), false, ""));
		ret.add(new TestVariableData("rVal", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoType.PGoUndetermined(), false, ""));

		return ret;
	}

	@Override
	public ArrayList<TestVariableData> getStageTypeVariables() {
		ArrayList<TestVariableData> ret = getStageOneVariables();
		ret.remove(2); // remove rVal
		ret.add(new TestVariableData("N", false, "<< \"defaultInitValue\" >>", "", false, new PGoPrimitiveType.PGoInt(),
				true, ""));
		return ret;
	}

	@Override
	public ArrayList<TestFunctionData> getStageOneFunctions() {
		ArrayList<TestFunctionData> ret = new ArrayList<TestFunctionData>();

		ArrayList<TestVariableData> params = new ArrayList<TestVariableData>();
		ArrayList<TestVariableData> vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("queens", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoCollectionType.PGoChan("int"), false, ""));
		params.add(new TestVariableData("i", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoInt(), false, ""));
		params.add(new TestVariableData("j", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoInt(), false, ""));

		String b = "[[label |-> \"attlabl\",\n stmts |-> <<[type |-> \"assignment\",\n              "
				+ "ass  |-> <<[lhs |-> [var |-> \"rVal\", sub |-> <<  >>],\n                          "
				+ "rhs |-> << \"\\\\/\", \"queens\", \"[\", \"i\", \"]\", \"=\", \"queens\", \"[\", \"j\", \"]\"\n, "
				+ "\"\\\\/\", \"queens\", \"[\", \"i\", \"]\", \"-\", \"queens\", \"[\", \"j\", \"]\", \"=\", \"i\", \"-\", \"j\"\n, "
				+ "\"\\\\/\", \"queens\", \"[\", \"j\", \"]\", \"-\", \"queens\", \"[\", \"i\", \"]\", \"=\", \"i\", \"-\", \"j\" >>]>>], \n"
				+ "             [type |-> \"return\", from |-> \"PGoAttacks\"]>>]]";

		ret.add(new TestFunctionData("PGoAttacks", params, vars, b, PGoFunction.FunctionType.Normal, false, "",
				new PGoPrimitiveType.PGoBool()));
		return ret;
	}

	@Override
	public ArrayList<TestFunctionData> getStageTypeFunctions() {
		ArrayList<TestFunctionData> ret = new ArrayList<TestFunctionData>();

		ArrayList<TestVariableData> params = new ArrayList<TestVariableData>();
		ArrayList<TestVariableData> vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("queens", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoCollectionType.PGoChan("int"), false, ""));
		params.add(new TestVariableData("i", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoInt(), false, ""));
		params.add(new TestVariableData("j", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoInt(), false, ""));

		vars.add(new TestVariableData("rVal", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoBool(), false, ""));

		String b = "[[label |-> \"attlabl\",\n stmts |-> <<[type |-> \"assignment\",\n              "
				+ "ass  |-> <<[lhs |-> [var |-> \"rVal\", sub |-> <<  >>],\n                          "
				+ "rhs |-> << \"\\\\/\", \"queens\", \"[\", \"i\", \"]\", \"=\", \"queens\", \"[\", \"j\", \"]\"\n, "
				+ "\"\\\\/\", \"queens\", \"[\", \"i\", \"]\", \"-\", \"queens\", \"[\", \"j\", \"]\", \"=\", \"i\", \"-\", \"j\"\n, "
				+ "\"\\\\/\", \"queens\", \"[\", \"j\", \"]\", \"-\", \"queens\", \"[\", \"i\", \"]\", \"=\", \"i\", \"-\", \"j\" >>]>>], \n"
				+ "             [type |-> \"return\", from |-> \"PGoAttacks\"]>>]]";

		ret.add(new TestFunctionData("Attacks", params, vars, b, PGoFunction.FunctionType.Normal, false, "",
				new PGoPrimitiveType.PGoBool()));
		return ret;
	}

	@Override
	protected String getAlg() {
		return "QueensPluscalProcedure";
	}

	@Override
	public int getNumGoroutineInit() {
		return 0;
	}

}
