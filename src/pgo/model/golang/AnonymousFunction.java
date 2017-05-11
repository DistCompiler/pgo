package pgo.model.golang;

import java.util.Vector;

import pgo.model.intermediate.PGoType;

/**
 * Represents an anonymous function in go
 *
 */
public class AnonymousFunction extends Expression {

	// the return type
	private PGoType retType;

	// the list of params
	private Vector<ParameterDeclaration> params;

	// the local variables
	private Vector<VariableDeclaration> localVars;

	// the body
	private Vector<Statement> body;

	// whether we call the function at declaration
	private boolean isCall;

	// the parameters the func is called with, if it is a function call; null otherwise
	private Vector<Expression> callParams;

	public AnonymousFunction(PGoType ret, Vector<ParameterDeclaration> params, Vector<VariableDeclaration> locals,
			Vector<Statement> vector) {
		this.retType = ret;
		this.params = params;
		this.localVars = locals;
		this.body = vector;
		this.isCall = false;
	}

	public AnonymousFunction(PGoType ret, Vector<ParameterDeclaration> params, Vector<VariableDeclaration> locals,
			Vector<Statement> body, Vector<Expression> callParams) {
		this.retType = ret;
		this.params = params;
		this.localVars = locals;
		this.body = body;
		this.isCall = true;
		this.callParams = callParams;
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
			ret.add("func(" + paramStr.remove(0));
			addIndented(ret, paramStr, true);
			ret.add(ret.remove(ret.size() - 1) + ") " + retType.toGo() + " {");
		} else {
			ret.add("func() " + retType.toGo() + " {");
		}
		addIndented(ret, localVars, false);
		addIndented(ret, body, false);
		if (this.isCall) {
			Vector<String> cParamStr = new Vector<String>();
			for (int i = 0; i < callParams.size(); i++) {
				Vector<String> e = callParams.get(i).toGo();
				for (int j = 0; j < e.size(); j++) {
					if (j > 0) {
						cParamStr.add(e.get(j));
					} else {
						if (i == 0) {
							cParamStr.add(e.get(j));
						} else {
							cParamStr.add(cParamStr.remove(cParamStr.size() - 1) + ", " + e.get(j));
						}
					}
				}
			}
			String add = "}";
			if (callParams.isEmpty()) {
				add += "()";
				ret.add(add);
			} else {
				add += "(" + cParamStr.remove(0);
				ret.add(add);
				addIndented(ret, cParamStr, true);
				ret.add(ret.remove(ret.size() - 1) + ")");
			}
		} else {
			ret.add("}");
		}
		
		return ret;
	}
}