package pgo.model.golang;

import java.util.Vector;

/**
 * A function call eg "foo(param1, param2)"
 * 
 */
public class FunctionCall extends Expression {

	// the called function
	private String fname;
	// the parameters
	private Vector<Expression> params;

	public FunctionCall(String fname, Vector<Expression> params) {
		this.fname = fname;
		this.params = params;
	}

	public String getFunction() {
		return fname;
	}

	public void setFunction(String f) {
		this.fname = f;
	}

	public Vector<Expression> getParams() {
		return params;
	}

	public void setParams(Vector<Expression> p) {
		this.params = p;
	}

	@Override
	public Vector<String> toGo() {
		Vector<String> paramStr = new Vector<String>();
		for (int i = 0; i < params.size(); i++) {
			Vector<String> e = params.get(i).toGo();
			for (int j = 0; j < e.size(); j++) {
				if (j > 0) {
					paramStr.add(e.get(j));
				} else {
					if (i == 0) {
						paramStr.add(e.get(j));
					} else {
						paramStr.add(paramStr.remove(paramStr.size() - 1) + ", " + e.get(j));
					}
				}
			}
		}
		Vector<String> ret = new Vector<String>();
		
		if (paramStr.size() > 0) {
			ret.add(fname + "(" + paramStr.remove(0));
			addIndented(ret, paramStr);
			ret.add(ret.remove(ret.size() - 1) + ")");
		} else {
			ret.add(fname + "()");
		}
		return ret;
	}

}
