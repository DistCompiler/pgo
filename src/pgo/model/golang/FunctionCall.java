package pgo.model.golang;

import java.util.Vector;

/**
 * A function call eg "foo(param1, param2)"
 * 
 */
public class FunctionCall extends Expression {

	// the called function name
	private String fname;
	// the parameters
	private Vector<Expression> params;

	public FunctionCall(String fname, Vector<Expression> params) {
		this.fname = fname;
		this.params = params;
	}

	public String getFunctionName() {
		return fname;
	}

	public void setFunctionName(String f) {
		this.fname = f;
	}

	public Vector<Expression> getParams() {
		return params;
	}

	public void setParams(Vector<Expression> p) {
		this.params = p;
	}

	@Override
	public String toGoExpr() {
		Vector<String> paramS = new Vector<String>(params.size());
		for (Expression e : params) {
			paramS.add(e.toGoExpr());
		}
		return fname + "(" + String.join(", ", paramS) + ")";
	}

}
