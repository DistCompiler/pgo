package pgo.trans.intermediate;

import pcal.AST.Macro;
import pcal.AST.Multiprocess;
import pcal.AST.Process;
import pgo.model.intermediate.PGoFunction;
import pgo.model.type.*;
import pgo.parser.PGoParseException;

import java.util.ArrayList;

/**
 * Tester class for the Sum PlusCal algorithm
 * 
 * This class stores the variables, functions and other data of the pluscal
 * algorithm to be used for validating the parsed and translated version of the
 * algorithm with the actual data.
 *
 */
public class SumIntermediateTester extends PGoPluscalStageTesterBase {

	@Override
	public boolean isMultiProcess() {
		return true;
	}

	public String getName() {
		return "Sum";
	}

	@Override
	public ArrayList<TestVariableData> getStageOneVariables() {
		ArrayList<TestVariableData> ret = new ArrayList<>();
		ret.add(new TestVariableData("network", true, "<< \"[\", \"i\", \"\\\\in\", "
				+ "\"1\", \"..\", \"N\", \"+\", \"1\", \"|->\", \"<<\", \">>\", \"]\" >>", "", false,
				new PGoTypeSlice(new PGoTypeChan(new PGoTypeSlice(PGoTypeInterface.getInstance()))), false, "", true));

		return ret;
	}

	@Override
	public ArrayList<TestVariableData> getStageTypeVariables() {
		ArrayList<TestVariableData> ret = getStageOneVariables();
		ret.add(new TestVariableData("MAXINT", true, "<< \"defaultInitValue\" >>", "10000000", true,
				PGoTypeNatural.getInstance(), false,
				"", false));
		ret.add(new TestVariableData("RUNS", true, "<< \"defaultInitValue\" >>", "", false,
				PGoTypeNatural.getInstance(), false, "runs", false));
		ret.add(new TestVariableData("N", true, "<< \"defaultInitValue\" >>", "", false,
				PGoTypeNatural.getInstance(), false, "numT", false));
		return ret;
	}

	@Override
	public ArrayList<TestFunctionData> getStageOneFunctions() throws PGoParseException {
		ArrayList<TestFunctionData> ret = new ArrayList<>();

		ArrayList<TestVariableData> params = new ArrayList<>();
		ArrayList<TestVariableData> vars = new ArrayList<>();
		params.add(new TestVariableData("from", true, "<< \"defaultInitValue\" >>", "", false,
				PGoTypeNatural.getInstance(), false, "", false));
		params.add(new TestVariableData("to", true, "<< \"defaultInitValue\" >>", "", false,
				PGoTypeNatural.getInstance(), false, "", false));
		params.add(new TestVariableData("msg", true, "<< \"defaultInitValue\" >>", "", false,
				PGoTypeInterface.getInstance(), false, "", false));

		String b = ((Macro) ((Multiprocess) getAST()).macros.get(0)).body.toString();

		ret.add(new TestFunctionData("SendTo", params, vars, b, PGoFunction.FunctionKind.Macro, false, "",
				PGoTypeVoid.getInstance()));

		params = new ArrayList<>();
		vars = new ArrayList<>();
		params.add(new TestVariableData("to", true, "<< \"defaultInitValue\" >>", "", false,
				   PGoTypeNatural.getInstance(), false, "", false));
		params.add(new TestVariableData("id", true, "<< \"defaultInitValue\" >>", "", false,
				   PGoTypeNatural.getInstance(), false, "", false));
		params.add(new TestVariableData("msg", true, "<< \"defaultInitValue\" >>", "", false,
				   PGoTypeInterface.getInstance(), false, "", false));

		b = ((Macro) ((Multiprocess) getAST()).macros.get(1)).body.toString();

		ret.add(new TestFunctionData("Recv", params, vars, b, PGoFunction.FunctionKind.Macro, false, "", PGoTypeVoid.getInstance()));

		params = new ArrayList<>();
		vars = new ArrayList<>();
		params.add(new TestVariableData("self", true, "<< \"defaultInitValue\" >>", "", false,
				   PGoTypeNatural.getInstance(), false, "", false));
		vars.add(new TestVariableData("a_init", true, "<< \"defaultInitValue\" >>", "", false,
				 PGoTypeNatural.getInstance(), false, "", false));
		vars.add(new TestVariableData("b_init", true, "<< \"defaultInitValue\" >>", "", false,
				 PGoTypeNatural.getInstance(), false, "", false));
		vars.add(new TestVariableData("runs", true, "<< \"0\" >>", "", false, PGoTypeNatural.getInstance(), false,
				"", false));
		vars.add(new TestVariableData("id", true, "<< \"defaultInitValue\" >>", "", false,
				 PGoTypeNatural.getInstance(), false, "", false));
		vars.add(new TestVariableData("msg", true, "<< \"defaultInitValue\" >>", "", false,
				 PGoTypeNatural.getInstance(), false, "", false));
		vars.add(new TestVariableData("sum", true, "<< \"defaultInitValue\" >>", "", false,
				 PGoTypeNatural.getInstance(), false, "", false));

		b = ((Process) ((Multiprocess) getAST()).procs.get(0)).body.toString();

		ret.add(new TestFunctionData("Client", params, vars, b, PGoFunction.FunctionKind.GoRoutine, false,
				"<< \"1\", \"..\", \"N\" >>", PGoTypeVoid.getInstance()));

		params = new ArrayList<>();
		vars = new ArrayList<>();
		params.add(new TestVariableData("self", true, "<< \"defaultInitValue\" >>", "", false,
				   PGoTypeNatural.getInstance(), false, "", false));
		vars.add(new TestVariableData("a", true, "<< \"defaultInitValue\" >>", "", false,
				 PGoTypeNatural.getInstance(), false, "", false));
		vars.add(new TestVariableData("b", true, "<< \"defaultInitValue\" >>", "", false,
				 PGoTypeNatural.getInstance(), false, "", false));
		vars.add(new TestVariableData("id", true, "<< \"defaultInitValue\" >>", "", false,
				 PGoTypeNatural.getInstance(), false, "", false));
		vars.add(new TestVariableData("msg", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoTypeSlice(PGoTypeNatural.getInstance()), false, "", false));

		b = ((Process) ((Multiprocess) getAST()).procs.get(1)).body.toString();

		ret.add(new TestFunctionData("Server", params, vars, b, PGoFunction.FunctionKind.GoRoutine, true,
				"<< \"N\", \"+\", \"1\" >>", PGoTypeVoid.getInstance()));

		return ret;
	}

	@Override
	protected String getAlg() {
		return "Sum";
	}

	@Override
	public int getNumGoroutineInit() {
		return 2;
	}
}
