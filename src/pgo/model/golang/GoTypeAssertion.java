package pgo.model.golang;

import pgo.model.golang.type.GoType;

import java.util.Objects;

/**
 * Represents a type assertion e.g. x.(int), which casts an interface to the
 * specified type.
 *
 */
public class GoTypeAssertion extends GoExpression {
	// the expr we are casting
	private GoExpression target;
	
	private GoType type;
	
	public GoTypeAssertion(GoExpression target, GoType type) {
		this.target = target;
		this.type = type;
	}
	
	public GoExpression getTarget() {
		return target;
	}
	
	public GoType getType() {
		return type;
	}

	@Override
	public <T, E extends Throwable> T accept(GoExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoTypeAssertion that = (GoTypeAssertion) o;
		return Objects.equals(target, that.target) &&
				Objects.equals(type, that.type);
	}

	@Override
	public int hashCode() {

		return Objects.hash(target, type);
	}
}
