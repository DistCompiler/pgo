package pgo.trans.intermediate;

import java.util.ArrayList;

import pcal.AST.Macro;
import pcal.AST.Multiprocess;
import pcal.AST.Process;
import pgo.model.intermediate.PGoCollectionType;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoType;
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
				+ " \"fred\", \"\\\"\", \"}\" >>", "", false, new PGoCollectionType.PGoSet("String"), false, ""));
				
		ret.add(new TestVariableData("restaurant_stage", true,
				"<< \"[\", \"mgr\", \"\\\\in\", \"managers\", \"|->\", \"\\\"\", \"start\", \"\\\"\", \"]\" >>", "",
				false, new PGoCollectionType.PGoMap("String", "String"), false, ""));
		return ret;
	}

	@Override
	public ArrayList<TestFunctionData> getStageOneFunctions() throws PGoParseException {
		ArrayList<TestFunctionData> ret = new ArrayList<TestFunctionData>();

		ArrayList<TestVariableData> params = new ArrayList<TestVariableData>();
		ArrayList<TestVariableData> vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("state", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoString(), false, ""));
		params.add(new TestVariableData("kmgrs", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoCollectionType.PGoSet("string"), false, ""));

		String b = ((Macro) ((Multiprocess) getAST()).macros.get(0)).body.toString();

		ret.add(new TestFunctionData("SetAll", params, vars, b, PGoFunction.FunctionType.Macro, false, "",
				PGoType.VOID));

		params = new ArrayList<TestVariableData>();
		vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("self", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoString(), false, ""));

		b = ((Process) ((Multiprocess) getAST()).procs.get(0)).body.toString();

		ret.add(new TestFunctionData("Restaurant", params, vars, b, PGoFunction.FunctionType.GoRoutine, false,
				"<< \"managers\" >>", PGoType.VOID));

		params = new ArrayList<TestVariableData>();
		vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("self", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoString(), false, ""));
		vars.add(new TestVariableData("rstMgrs", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoCollectionType.PGoSet("String"), false, ""));
		vars.add(new TestVariableData("aborted", true, "<< \"FALSE\" >>", "", false, new PGoPrimitiveType.PGoBool(),
				false, ""));
		
		b = ((Process) ((Multiprocess) getAST()).procs.get(1)).body.toString();

		ret.add(new TestFunctionData("Controller", params, vars, b, PGoFunction.FunctionType.GoRoutine, true,
				"<< \"\\\"\", \"alice\", \"\\\"\" >>", PGoType.VOID));
		
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
