package pgo.model.golang;

public class Go extends Statement {
	private Expression expression;

	public Go(Expression expression) {
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
