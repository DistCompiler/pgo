package pgo.model.tla;

import pgo.util.SourceLocation;

/*
 * Represents `expr.field`.
 */
public class TLADot extends TLAExpression {
	private final TLAExpression expression;
	private final String field;

	public TLADot(SourceLocation location, TLAExpression expression, String field) {
		super(location);
		this.expression = expression;
		this.field = field;
	}

	@Override
	public int hashCode() {
		return expression.hashCode() * 17 + field.hashCode() * 19 + 3;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (!(obj instanceof TLADot)) {
			return false;
		}
		TLADot other = (TLADot) obj;
		return expression.equals(other.expression) && field.equals(other.field);
	}

	@Override
	public TLAExpression copy() {
		return new TLADot(getLocation(), expression.copy(), field);
	}

	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public TLAExpression getExpression() {
		return expression;
	}

	public String getField() {
		return field;
	}
}
