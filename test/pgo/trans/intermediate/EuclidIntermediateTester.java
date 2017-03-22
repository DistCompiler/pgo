package pgo.trans.intermediate;

import java.util.ArrayList;

/**
 * Tester class for the Euclid pluscal algorithm
 * 
 * This class stores the variables, functions and other data of the pluscal
 * algorithm to be used for validating the parsed and translated version of the
 * algorithm with the actual data.
 *
 */
public class EuclidIntermediateTester extends PGoPluscalStageOneTesterBase {

	@Override
	public boolean isMultiProcess() {
		return false;
	}

	public String getName() {
		return "Euclid";
	}

	@Override
	public ArrayList<TestVariableData> getVariables() {
		ArrayList<TestVariableData> ret = new ArrayList<TestVariableData>();
		ret.add(new TestVariableData("u", true, "<< \"24\" >>"));
		ret.add(new TestVariableData("v", false, "<< \"1\", \"..\", \"N\" >>"));
		ret.add(new TestVariableData("v_init", true, "<< \"v\" >>"));

		return ret;
	}

	@Override
	public ArrayList<TestFunctionData> getFunctions() {
		return new ArrayList<TestFunctionData>();
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
