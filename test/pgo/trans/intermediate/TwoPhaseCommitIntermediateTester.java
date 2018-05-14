package pgo.trans.intermediate;

import java.util.ArrayList;

import pcal.AST.Macro;
import pcal.AST.Multiprocess;
import pcal.AST.Process;
import pgo.model.intermediate.PGoCollectionType;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.type.*;
import pgo.parser.PGoParseException;

/**
 * Tester class for the TwoPhaseCommit pluscal algorithm
 * 
 * This class stores the variables, functions and other data of the pluscal
 * algorithm to be used for validating the parsed and translated version of the
 * algorithm with the actual data.
 *
 */
public class TwoPhaseCommitIntermediateTester extends PGoPluscalStageTesterBase {

	@Override
	public boolean isMultiProcess() {
		return true;
	}

	public String getName() {
		return "TwoPhaseCommit";
	}

	@Override
	public ArrayList<TestVariableData> getStageOneVariables() {
		ArrayList<TestVariableData> ret = new ArrayList<TestVariableData>();
		ret.add(new TestVariableData("managers", true,"<< \"{\", \"\\\"\", \"bob\", \"\\\"\","
				+ " \",\", \"\\\"\", \"chuck\", \"\\\"\", \",\", \"\\\"\", \"dave\", "
				+ "\"\\\"\", \",\", \"\\\"\", \"everett\", \"\\\"\", \",\", \"\\\"\","
				+ " \"fred\", \"\\\"\", \"}\" >>", "", false, new PGoTypeSet(PGoTypeString.getInstance()), false, "", false));
				
		ret.add(new TestVariableData("restaurant_stage", true,
				"<< \"[\", \"mgr\", \"\\\\in\", \"managers\", \"|->\", \"\\\"\", \"start\", \"\\\"\", \"]\" >>", "",
				false, new PGoTypeMap(PGoTypeString.getInstance(), PGoTypeString.getInstance()), false, "", true));
		return ret;
	}

	@Override
	public ArrayList<TestFunctionData> getStageOneFunctions() throws PGoParseException {
		ArrayList<TestFunctionData> ret = new ArrayList<>();

		ArrayList<TestVariableData> params = new ArrayList<>();
		ArrayList<TestVariableData> vars = new ArrayList<>();
		params.add(new TestVariableData("state", true, "<< \"defaultInitValue\" >>", "", false,
				   PGoTypeString.getInstance(), false, "", false));
		params.add(new TestVariableData("kmgrs", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoTypeSet(PGoTypeString.getInstance()), false, "", false));

		String b = ((Macro) ((Multiprocess) getAST()).macros.get(0)).body.toString();

		ret.add(new TestFunctionData("SetAll", params, vars, b, PGoFunction.FunctionKind.Macro, false, "",
				PGoTypeVoid.getInstance()));

		params = new ArrayList<>();
		vars = new ArrayList<>();
		params.add(new TestVariableData("self", true, "<< \"defaultInitValue\" >>", "", false,
				   PGoTypeString.getInstance(), false, "", false));

		b = ((Process) ((Multiprocess) getAST()).procs.get(0)).body.toString();

		ret.add(new TestFunctionData("Restaurant", params, vars, b, PGoFunction.FunctionKind.GoRoutine, false,
				"<< \"managers\" >>", PGoTypeVoid.getInstance()));

		params = new ArrayList<>();
		vars = new ArrayList<>();
		params.add(new TestVariableData("self", true, "<< \"defaultInitValue\" >>", "", false,
				   PGoTypeString.getInstance(), false, "", false));
		vars.add(new TestVariableData("rstMgrs", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoTypeSet(PGoTypeString.getInstance()), false, "", false));
		vars.add(new TestVariableData("aborted", true, "<< \"FALSE\" >>", "", false, PGoTypeBool.getInstance(),
				false, "", false));
		
		b = ((Process) ((Multiprocess) getAST()).procs.get(1)).body.toString();

		ret.add(new TestFunctionData("Controller", params, vars, b, PGoFunction.FunctionKind.GoRoutine, true,
				"<< \"\\\"\", \"alice\", \"\\\"\" >>", PGoTypeVoid.getInstance()));
		
		return ret;
	}

	@Override
	protected String getAlg() {
		return "TwoPhaseCommit";
	}

	@Override
	public int getNumGoroutineInit() {
		return 2;
	}

}
