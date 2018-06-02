package pgo.model.golang;

public class Defer extends Statement {
	private Expression expression;

	public Defer(Expression expression) {
		this.expression = expression;
	}

	public Expression getExpression() {
		return expression;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
