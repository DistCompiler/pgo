package pgo.model.golang;

import java.util.Vector;

/**
 * A goroutine call
 *
 */
public class GoCall extends Expression {

	private FunctionCall func;

	public GoCall(FunctionCall f) {
		func = f;
	}

	public FunctionCall getFunctionCall() {
		return func;
	}

	public void setFunctionCall(FunctionCall f) {
		this.func = f;
	}

	@Override
	public Vector<String> toGo() {
		Vector<String> ret = new Vector<String>();
		Vector<String> funcStr = func.toGo();
		
		ret.add("go " + funcStr.remove(0));
		ret.addAll(funcStr);

		return ret;
	}

}
