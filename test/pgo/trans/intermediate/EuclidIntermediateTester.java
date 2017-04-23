package pgo.trans.intermediate;

import java.util.ArrayList;

import pgo.model.intermediate.PGoPrimitiveType;

/**
 * Tester class for the Euclid pluscal algorithm
 * 
 * This class stores the variables, functions and other data of the pluscal
 * algorithm to be used for validating the parsed and translated version of the
 * algorithm with the actual data.
 *
 */
public class EuclidIntermediateTester extends PGoPluscalStageTesterBase {

	@Override
	public boolean isMultiProcess() {
		return false;
	}

	public String getName() {
		return "Euclid";
	}

	@Override
	public ArrayList<TestVariableData> getStageOneVariables() {
		ArrayList<TestVariableData> ret = new ArrayList<TestVariableData>();
		ret.add(new TestVariableData("u", true, "<< \"24\" >>", "", false, new PGoPrimitiveType.PGoInt(), false, ""));
		ret.add(new TestVariableData("v", false, "<< \"1\", \"..\", \"N\" >>", "", false, new PGoPrimitiveType.PGoInt(),
				false, ""));
		ret.add(new TestVariableData("v_init", true, "<< \"v\" >>", "", false, new PGoPrimitiveType.PGoInt(), false,
				""));

		return ret;
	}

	@Override
	public ArrayList<TestFunctionData> getStageOneFunctions() {
		return new ArrayList<TestFunctionData>();
	}

	@Override
	public ArrayList<TestVariableData> getStageTypeVariables() {
		ArrayList<TestVariableData> ret = super.getStageTypeVariables();
		ret.add(new TestVariableData("N", false, "<< \"defaultInitValue\" >>", "", false, new PGoPrimitiveType.PGoInt(),
				true, ""));
		return ret;
	}

	@Override
	public int getNumGoroutineInit() {
		return 0;
	}

	@Override
	protected String getAlg() {
		return "Euclid";
	}

}
