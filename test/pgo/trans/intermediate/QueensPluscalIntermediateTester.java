package pgo.trans.intermediate;

import java.util.ArrayList;

import pgo.model.type.PGoTypeInt;
import pgo.model.type.PGoTypeSet;
import pgo.model.type.PGoTypeSlice;

/**
 * Tester class for the QueensPluscal pluscal algorithm
 *
 * This class stores the variables, functions and other data of the pluscal
 * algorithm to be used for validating the parsed and translated version of the
 * algorithm with the actual data.
 *
 */
public class QueensPluscalIntermediateTester extends PGoPluscalStageTesterBase {

	@Override
	public boolean isMultiProcess() {
		return false;
	}

	public String getName() {
		return "QueensPluscal";
	}

	@Override
	public ArrayList<TestVariableData> getStageOneVariables() {
		ArrayList<TestVariableData> ret = new ArrayList<TestVariableData>();
		ret.add(new TestVariableData("todo", true, "<< \"{\", \"<<\", \">>\", \"}\" >>", "", false,
				new PGoTypeSet(new PGoTypeSlice(PGoTypeInt.getInstance())), false, "", false));
		ret.add(new TestVariableData("sols", true, "<< \"{\", \"}\" >>", "", false,
				new PGoTypeSet(new PGoTypeSlice(PGoTypeInt.getInstance())), false, "", false));

		return ret;
	}

	@Override
	public ArrayList<TestVariableData> getStageTypeVariables() {
		ArrayList<TestVariableData> ret = getStageOneVariables();
		ret.add(new TestVariableData("N", true, "<< \"defaultInitValue\" >>", "", false, PGoTypeInt.getInstance(),
				true, "", false));
		return ret;
	}

	@Override
	public ArrayList<TestFunctionData> getStageOneFunctions() {
		return new ArrayList<>();
	}

	@Override
	protected String getAlg() {
		return "QueensPluscal";
	}

	@Override
	public int getNumGoroutineInit() {
		return 0;
	}
}
