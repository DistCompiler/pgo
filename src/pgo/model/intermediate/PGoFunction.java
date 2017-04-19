package pgo.model.intermediate;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.Vector;

import pcal.AST;
import pcal.AST.Macro;
import pcal.AST.PVarDecl;
import pcal.AST.Procedure;
import pcal.AST.Process;
import pcal.AST.VarDecl;

/**
 * Intermediate representation of a single pluscal and golang function.
 * 
 * PlusCal declares functions as macros, procedures, and TLAExpr (for boolean
 * outputs) Intermediate representation parses out the basic information without
 * fully converting to go
 *
 */
public class PGoFunction {

	// The function name
	private String funcName;

	// The parameters to the function
	private LinkedHashMap<String, PGoVariable> params;

	// The declared variables of the function
	private LinkedHashMap<String, PGoVariable> vars;

	// The body of the function
	private Vector<AST> body;

	// Whether this function is a goroutine or procese, or a macro, or a
	// standard function
	private FunctionType type;

	public static enum FunctionType {
		GoRoutine, Macro, Normal
	}

	// The line number at start of function
	private int line;

	public String getName() {
		return funcName;
	}

	public ArrayList<PGoVariable> getParams() {
		return new ArrayList<PGoVariable>(params.values());
	}

	public PGoVariable getParam(String p) {
		return params.get(p);
	}

	public ArrayList<PGoVariable> getVariables() {
		return new ArrayList<PGoVariable>(vars.values());
	}

	public PGoVariable getVariable(String v) {
		return vars.get(v);
	}

	public Vector<AST> getBody() {
		return body;
	}

	public FunctionType getType() {
		return type;
	}

	public int getLine() {
		return line;
	}

	// private constructor
	private PGoFunction() {
		params = new LinkedHashMap<String, PGoVariable>();
		vars = new LinkedHashMap<String, PGoVariable>();
		body = new Vector<AST>();
		type = FunctionType.Normal;
	}

	// Converts a procedure from pluscal into a golang function
	public static PGoFunction convert(Procedure m) {
		PGoFunction ret = new PGoFunction();
		ret.funcName = m.name;
		for (PVarDecl var : (Vector<PVarDecl>) m.params) {
			PGoVariable pvar = PGoVariable.convert(var);
			ret.params.put(pvar.getName(), pvar);
		}
		for (PVarDecl var : (Vector<PVarDecl>) m.decls) {
			PGoVariable pvar = PGoVariable.convert(var);
			ret.vars.put(pvar.getName(), pvar);
		}

		ret.body = m.body;
		ret.line = m.line;

		return ret;
	}

	// Converts a macro from pluscal into a golang function
	public static PGoFunction convert(Macro m) {
		PGoFunction ret = new PGoFunction();
		ret.funcName = m.name;
		for (String var : (Vector<String>) m.params) {
			PGoVariable pvar = PGoVariable.convert(var);
			ret.params.put(pvar.getName(), pvar);
		}

		ret.body = m.body;
		ret.type = FunctionType.Macro;
		ret.line = m.line;

		return ret;
	}

	// Converts a process from a multiprocessed pluscal algorithm to a go
	// function that we can run as a goroutine
	public static PGoFunction convert(Process p) {
		PGoFunction ret = new PGoFunction();
		ret.funcName = p.name;

		// process function argument is just the process id
		PGoVariable id = PGoVariable.processIdArg();
		ret.params.put(id.getName(), id);

		for (VarDecl var : (Vector<VarDecl>) p.decls) {
			PGoVariable pvar = PGoVariable.convert(var);
			ret.vars.put(pvar.getName(), pvar);
		}

		ret.body = p.body;
		ret.line = p.line;
		ret.type = FunctionType.GoRoutine;

		return ret;
	}

}
