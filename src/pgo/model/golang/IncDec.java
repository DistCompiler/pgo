package pgo.model.golang;

import java.util.Objects;

public class IncDec extends Statement {
	
	private boolean inc;
	private Expression expression;

	public IncDec(boolean inc, Expression expression) {
		this.inc = inc;
		this.expression = expression;
	}

	public boolean isInc() {
		return inc;
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
		IncDec incDec = (IncDec) o;
		return inc == incDec.inc &&
				Objects.equals(expression, incDec.expression);
	}

	@Override
	public int hashCode() {

		return Objects.hash(inc, expression);
	}
}
