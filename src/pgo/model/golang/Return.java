package pgo.model.golang;

/**
 * A return keyword in go
 *
 */
public class Return extends Expression {

	// the return value if any
	private Expression value;

	public Return(Expression value) {
		this.value = value;
	}

	public Expression getExpression() {
		return value;
	}

	public void setExpression(Expression e) {
		this.value = e;
	}

	@Override
	public String toGoExpr() {
		return "return" + (value == null ? "" : " " + value.toGoExpr());
	}

}
