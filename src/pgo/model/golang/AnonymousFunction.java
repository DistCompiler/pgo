package pgo.model.golang;

import java.util.List;
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
	private List<ParameterDeclaration> params;

	// the local variables
	private List<VariableDeclaration> localVars;

	// the body
	private List<Statement> body;

	// whether we call the function at declaration
	private boolean isCall;

	// the parameters the func is called with, if it is a function call; null otherwise
	private List<Expression> callParams;

	public AnonymousFunction(PGoType ret, List<ParameterDeclaration> params, List<VariableDeclaration> locals,
							 List<Statement> vector) {
		this.retType = ret;
		this.params = params;
		this.localVars = locals;
		this.body = vector;
		this.isCall = false;
	}

	public AnonymousFunction(PGoType ret, List<ParameterDeclaration> params, List<VariableDeclaration> locals,
							 List<Statement> body, List<Expression> callParams) {
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

	public List<ParameterDeclaration> getParameter() {
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
	public List<String> toGo() {
		List<String> ret = new Vector<>();
		List<String> paramStr = new Vector<>();

		for (int i = 0; i < params.size(); i++) {
			List<String> e = params.get(i).toGo();
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
			addStringsAndIndent(ret, paramStr);
			ret.add(ret.remove(ret.size() - 1) + ") " + retType.toGo() + " {");
		} else {
			ret.add("func() " + retType.toGo() + " {");
		}
		addIndentedAST(ret, localVars);
		addIndentedAST(ret, body);
		if (this.isCall) {
			Vector<String> cParamStr = new Vector<String>();
			for (int i = 0; i < callParams.size(); i++) {
				List<String> e = callParams.get(i).toGo();
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
				addStringsAndIndent(ret, cParamStr);
				ret.add(ret.remove(ret.size() - 1) + ")");
			}
		} else {
			ret.add("}");
		}
		
		return ret;
	}
}