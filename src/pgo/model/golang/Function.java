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

	public Vector<Statement> getBody() {
		return body;
	}

	public void setBody(Vector<Statement> body) {
		this.body = body;
	}

	@Override
	public Vector<String> toGo() {
		Vector<String> ret = new Vector<String>();
		Vector<String> paramStr = new Vector<String>();

		for (int i = 0; i < params.size(); i++) {
			Vector<String> e = params.get(i).toGo();
			for (int j = 0; j < e.size(); j++) {
				if (j > 0) {
					paramStr.add(e.get(j));
				} else {
					// param is one line
					if (i == 0) {
						paramStr.add(e.get(j));
					} else {
						paramStr.add(paramStr.remove(paramStr.size() - 1) + ", " + e.get(j));
					}
				}
			}
		}
		if (paramStr.size() > 0) {
			ret.add("func " + fname + "(" + paramStr.remove(0));
			addIndented(ret, paramStr);
			ret.add(ret.remove(ret.size() - 1) + ") " + retType.toGo() + " {");
		} else {
			ret.add("func " + fname + "() " + retType.toGo() + " {");
		}
		addIndented(ret, localVars);
		addIndented(ret, body);
		ret.add("}");
		return ret;
	}
}