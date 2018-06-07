package pgo.model.golang;

import java.util.Objects;

public class ExpressionStatement extends Statement {

	private Expression expression;

	public ExpressionStatement(Expression expression) {
		this.expression = expression;
	}

	public Expression getExpression() {
		return expression;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		ExpressionStatement that = (ExpressionStatement) o;
		return Objects.equals(expression, that.expression);
	}

	@Override
	public int hashCode() {

		return Objects.hash(expression);
	}
}
