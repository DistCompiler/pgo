package pgo.model.golang;

import java.util.Vector;

import pgo.model.intermediate.PGoType;

/**
 * Represents a function in go
 *
 */
public class Function extends GoAST {
	// the function name
	private final String fname;

	// the return type
	private PGoType retType;

	// the list of params
	private Vector<ParameterDeclaration> params;

	// the local variables
	private Vector<VariableDeclaration> localVars;

	// the body
	private Vector<Statement> body;

	public Function(String name, PGoType ret, Vector<ParameterDeclaration> params,
			Vector<VariableDeclaration> locals, Vector<Statement> vector) {
		this.fname = name;
		this.retType = ret;
		this.params = params;
		this.localVars = locals;
		this.body = vector;
	}

	public String getName() {
		return fname;
	}

	public PGoType getReturnType() {
		return retType;
	}

	public void setReturnType(PGoType t) {
		this.retType = t;
	}

	public Vector<ParameterDeclaration> getParameter() {
		return params;
	}

	public void addParameter(ParameterDeclaration p) {
		params.add(p);
	}

	public void insertParameter(ParameterDeclaration p, int i) {
		params.add(i, p);
	}

	public void removeParameter(ParameterDeclaration p) {
		params.remove(p);
	}

	public Vector<VariableDeclaration> getLocalVariables() {
		return new Vector<VariableDeclaration>(localVars);
	}

	public void setLocalVariables(Vector<VariableDeclaration> s) {
		this.localVars = s;
	}

	@Override
	public Vector<String> toGo() {
		Vector<String> ret = new Vector<String>();
		Vector<String> pnames = new Vector<String>();
		for (ParameterDeclaration p : params) {
			pnames.add(p.toGoExpr());
		}
		ret.add("func " + fname + "(" + String.join(", ", pnames) + ") " + retType.toGo() + " {");
		addIndented(ret, localVars);
		addIndented(ret, body);
		ret.add("}");
		return ret;
	}
}