package pgo.trans.intermediate.model;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.Vector;

import pcal.AST;
import pcal.AST.Macro;
import pcal.AST.PVarDecl;
import pcal.AST.Procedure;

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

	// private constructor
	private PGoFunction() {
		params = new LinkedHashMap<String, PGoVariable>();
		vars = new LinkedHashMap<String, PGoVariable>();
		body = new Vector<AST>();
	}

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

		return ret;
	}

	public static PGoFunction convert(Macro m) {
		PGoFunction ret = new PGoFunction();
		ret.funcName = m.name;
		for (String var : (Vector<String>) m.params) {
			PGoVariable pvar = PGoVariable.convert(var);
			ret.params.put(pvar.getName(), pvar);
		}

		ret.body = m.body;

		return ret;
	}

}
