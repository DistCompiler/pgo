package pgo.model.golang;

import java.util.Objects;

public class GoDefer extends GoStatement {
	private final GoExpression expression;

	public GoDefer(GoExpression expression) {
		this.expression = expression;
	}

	public GoExpression getExpression() {
		return expression;
	}

	@Override
	public <T, E extends Throwable> T accept(GoStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoDefer defer = (GoDefer) o;
		return Objects.equals(expression, defer.expression);
	}

	@Override
	public int hashCode() {

		return Objects.hash(expression);
	}
}
