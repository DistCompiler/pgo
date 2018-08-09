package pgo.model.golang;

import java.util.Objects;

public class GoIncDec extends GoStatement {
	
	private boolean inc;
	private GoExpression expression;

	public GoIncDec(boolean inc, GoExpression expression) {
		this.inc = inc;
		this.expression = expression;
	}

	public boolean isInc() {
		return inc;
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
		GoIncDec incDec = (GoIncDec) o;
		return inc == incDec.inc &&
				Objects.equals(expression, incDec.expression);
	}

	@Override
	public int hashCode() {

		return Objects.hash(inc, expression);
	}
}
