package pgo.model.golang;

import java.util.List;
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
	private List<ParameterDeclaration> params;

	// the local variables
	private List<VariableDeclaration> localVars;

	// the body
	private List<Statement> body;

	public Function(String name, PGoType ret, List<ParameterDeclaration> params,
					List<VariableDeclaration> locals, List<Statement> vector) {
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

	public List<VariableDeclaration> getLocalVariables() {
		return new Vector<>(localVars);
	}

	public void setLocalVariables(Vector<VariableDeclaration> s) {
		this.localVars = s;
	}

	public List<Statement> getBody() {
		return body;
	}

	public void setBody(List<Statement> body) {
		this.body = body;
	}

	@Override
	public List<String> toGo() {
		Vector<String> ret = new Vector<>();
		Vector<String> paramStr = new Vector<>();

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
			ret.add("func " + fname + "(" + paramStr.remove(0));
			addStringsAndIndent(ret, paramStr);
			ret.add(ret.remove(ret.size() - 1) + ") " + retType.toGo() + " {");
		} else {
			ret.add("func " + fname + "() " + retType.toGo() + " {");
		}
		addIndentedAST(ret, localVars);
		addIndentedAST(ret, body);
		ret.add("}");
		return ret;
	}
}