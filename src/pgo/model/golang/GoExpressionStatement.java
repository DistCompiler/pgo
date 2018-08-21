package pgo.model.golang;

import java.util.Objects;

public class GoExpressionStatement extends GoStatement {

	private GoExpression expression;

	public GoExpressionStatement(GoExpression expression) {
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
		GoExpressionStatement that = (GoExpressionStatement) o;
		return Objects.equals(expression, that.expression);
	}

	@Override
	public int hashCode() {

		return Objects.hash(expression);
	}
}
