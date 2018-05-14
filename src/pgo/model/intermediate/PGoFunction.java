package pgo.model.intermediate;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Vector;

import pcal.AST;
import pcal.AST.Macro;
import pcal.AST.PVarDecl;
import pcal.AST.Procedure;
import pcal.AST.Process;
import pcal.AST.VarDecl;
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeGenerator;
import pgo.model.type.PGoTypeVoid;

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
	private List<AST> body;

	public enum FunctionKind {
		GoRoutine, Macro, Normal, Process
	}

	// Whether this function is a goroutine, a macro, a standard function, or a process
	private FunctionKind kind;

	// The return type of the function
	private PGoType rType;

	// The line number at start of function
	private int line;

	public String getName() {
		return funcName;
	}

	// Get the return type
	public PGoType getReturnType() {
		return rType;
	}

	// set the return kind
	public void setReturnType(PGoType t) {
		this.rType = t;
	}

	// Updates the name of the function
	public void setName(String name) {
		this.funcName = name;
	}

	public ArrayList<PGoVariable> getParams() {
		return new ArrayList<>(params.values());
	}

	public PGoVariable getParam(String p) {
		return params.get(p);
	}

	public ArrayList<PGoVariable> getVariables() {
		return new ArrayList<>(vars.values());
	}

	public PGoVariable getVariable(String v) {
		return vars.get(v);
	}

	public void addVariable(PGoVariable retVar) {
		vars.put(retVar.getName(), retVar);
	}

	public List<AST> getBody() {
		return body;
	}

	public FunctionKind getKind() {
		return kind;
	}

	public int getLine() {
		return line;
	}

	// hide the constructor
	private PGoFunction(String name, PGoType returnType, List<AST> body) {
		funcName = name;
		params = new LinkedHashMap<>();
		vars = new LinkedHashMap<>();
		this.body = body;
		kind = FunctionKind.Normal;
		rType = returnType;
	}

	// Converts a procedure from pluscal into a golang function
	public static PGoFunction convert(Procedure m, PGoTypeGenerator generator) {
		PGoFunction ret = new PGoFunction(m.name, generator.get(), m.body);
		for (PVarDecl var : (Vector<PVarDecl>) m.params) {
			PGoVariable pvar = PGoVariable.convert(var, generator.get());
			pvar.setLine(m.line);
			ret.params.put(pvar.getName(), pvar);
		}
		for (PVarDecl var : (Vector<PVarDecl>) m.decls) {
			PGoVariable pvar = PGoVariable.convert(var, generator.get());
			ret.vars.put(pvar.getName(), pvar);
		}
		ret.line = m.line;
		return ret;
	}

	// Converts a macro from pluscal into a golang function
	public static PGoFunction convert(Macro m, PGoTypeGenerator generator) {
		PGoFunction ret = new PGoFunction(m.name, PGoTypeVoid.getInstance(), m.body);
		for (String var : (Vector<String>) m.params) {
			PGoVariable pvar = PGoVariable.convert(var, generator.get());
			pvar.setLine(m.line);
			ret.params.put(pvar.getName(), pvar);
		}
		ret.kind = FunctionKind.Macro;
		ret.line = m.line;
		return ret;
	}

	// Converts a process from a multiprocessed pluscal algorithm to a go
	// function that we can run as a goroutine
	public static PGoFunction convert(Process p, FunctionKind kind, PGoTypeGenerator generator) {
		PGoFunction ret = new PGoFunction(p.name, PGoTypeVoid.getInstance(), p.body);
		// process function argument is just the process id
		PGoVariable id = PGoVariable.processIdArg(generator.get());
		ret.params.put(id.getName(), id);
		for (VarDecl var : (Vector<VarDecl>) p.decls) {
			PGoVariable pvar = PGoVariable.convert(var, generator.get());
			ret.vars.put(pvar.getName(), pvar);
		}
		ret.line = p.line;
		ret.kind = kind;
		return ret;
	}

}
