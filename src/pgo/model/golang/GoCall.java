package pgo.model.golang;

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
	public String toGoExpr() {
		return "go " + func.toGoExpr();
	}

}
