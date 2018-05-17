package pgo.model.golang;

import java.util.List;
import java.util.Vector;

/**
 * A function call eg "foo(param1, param2)"
 * 
 */
public class FunctionCall extends Expression {

	// the called function
	private String fname;
	// the parameters
	private List<Expression> params;
	// whether this is an object call
	private boolean isObjectCall;
	// the object the function is called on; null if this is not an object call
	private Expression obj;

	public FunctionCall(String fname, List<Expression> params) {
		this.fname = fname;
		this.params = params;
		this.isObjectCall = false;
	}
	
	public FunctionCall(String fname, List<Expression> params, Expression obj) {
		this.fname = fname;
		this.params = params;
		this.obj = obj;
		this.isObjectCall = true;
	}

	public String getFunction() {
		return fname;
	}

	public void setFunction(String f) {
		this.fname = f;
	}

	public List<Expression> getParams() {
		return params;
	}

	public void setParams(Vector<Expression> p) {
		this.params = p;
	}
	
	public Expression getObj() {
		return obj;
	}

	@Override
	public List<String> toGo() {
		Vector<String> paramStr = new Vector<>();
		for (int i = 0; i < params.size(); i++) {
			List<String> e = params.get(i).toGo();
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
		Vector<String> ret = new Vector<>();
		String first = "";
		if (this.isObjectCall) {
			assert (obj != null);
			assert (obj.toGo().size() == 1);
			first = obj.toGo().get(0) + ".";
		} else {
			assert (obj == null);
		}
		if (paramStr.size() > 0) {
			first += fname + "(" + paramStr.remove(0);
			ret.add(first);
			addStringsAndIndent(ret, paramStr);
			ret.add(ret.remove(ret.size() - 1) + ")");
		} else {
			first += fname + "()";
			ret.add(first);
		}
		return ret;
	}
}
