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
 * Tester class for the Sum pluscal algorithm
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
		ArrayList<TestVariableData> ret = new ArrayList<TestVariableData>();
		ret.add(new TestVariableData("network", true, "<< \"[\", \"i\", \"\\\\in\", "
				+ "\"1\", \"..\", \"N\", \"+\", \"1\", \"|->\", \"<<\", \">>\", \"]\" >>", "", false,
				new PGoCollectionType.PGoSlice("chan[[2]interface]"), false, ""));

		return ret;
	}

	@Override
	public ArrayList<TestVariableData> getStageTypeVariables() {
		ArrayList<TestVariableData> ret = getStageOneVariables();
		ret.add(new TestVariableData("MAXINT", true, "<< \"defaultInitValue\" >>", "10000000", true,
				new PGoPrimitiveType.PGoNatural(), false,
				""));
		ret.add(new TestVariableData("RUNS", false, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, "runs"));
		ret.add(new TestVariableData("N", false, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, "numT"));
		return ret;
	}

	@Override
	public ArrayList<TestFunctionData> getStageOneFunctions() throws PGoParseException {
		ArrayList<TestFunctionData> ret = new ArrayList<TestFunctionData>();

		ArrayList<TestVariableData> params = new ArrayList<TestVariableData>();
		ArrayList<TestVariableData> vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("from", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, ""));
		params.add(new TestVariableData("to", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, ""));
		params.add(new TestVariableData("msg", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoInterface(), false, ""));

		String b = ((Macro) ((Multiprocess) getAST()).macros.get(0)).body.toString();

		ret.add(new TestFunctionData("SendTo", params, vars, b, PGoFunction.FunctionType.Macro, false, "",
				PGoType.VOID));

		params = new ArrayList<TestVariableData>();
		vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("to", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, ""));
		params.add(new TestVariableData("id", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, ""));
		params.add(new TestVariableData("msg", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoInterface(), false, ""));

		b = ((Macro) ((Multiprocess) getAST()).macros.get(1)).body.toString();

		ret.add(new TestFunctionData("Recv", params, vars, b, PGoFunction.FunctionType.Macro, false, "", PGoType.VOID));

		params = new ArrayList<TestVariableData>();
		vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("self", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, ""));
		vars.add(new TestVariableData("a_init", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, ""));
		vars.add(new TestVariableData("b_init", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, ""));
		vars.add(new TestVariableData("runs", true, "<< \"0\" >>", "", false, new PGoPrimitiveType.PGoNatural(), false,
				""));
		vars.add(new TestVariableData("id", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, ""));
		vars.add(new TestVariableData("msg", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, ""));
		vars.add(new TestVariableData("sum", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, ""));

		b = ((Process) ((Multiprocess) getAST()).procs.get(0)).body.toString();

		ret.add(new TestFunctionData("Client", params, vars, b, PGoFunction.FunctionType.GoRoutine, false,
				"<< \"1\", \"..\", \"N\" >>", PGoType.VOID));

		params = new ArrayList<TestVariableData>();
		vars = new ArrayList<TestVariableData>();
		params.add(new TestVariableData("self", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, ""));
		vars.add(new TestVariableData("a", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, ""));
		vars.add(new TestVariableData("b", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, ""));
		vars.add(new TestVariableData("id", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoPrimitiveType.PGoNatural(), false, ""));
		vars.add(new TestVariableData("msg", true, "<< \"defaultInitValue\" >>", "", false,
				new PGoCollectionType.PGoSlice("2", "uint64"), false, ""));

		b = ((Process) ((Multiprocess) getAST()).procs.get(1)).body.toString();

		ret.add(new TestFunctionData("Server", params, vars, b, PGoFunction.FunctionType.GoRoutine, true,
				"<< \"N\", \"+\", \"1\" >>", PGoType.VOID));

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
