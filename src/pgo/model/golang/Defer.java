package pgo.model.golang;

import java.util.Objects;

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

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		Defer defer = (Defer) o;
		return Objects.equals(expression, defer.expression);
	}

	@Override
	public int hashCode() {

		return Objects.hash(expression);
	}
}
