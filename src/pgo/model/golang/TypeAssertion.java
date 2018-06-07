package pgo.model.golang;

import java.util.Objects;

/**
 * Represents a type assertion e.g. x.(int), which casts an interface to the
 * specified type.
 *
 */
public class TypeAssertion extends Expression {
	// the expr we are casting
	private Expression target;
	
	private Type type;
	
	public TypeAssertion(Expression target, Type type) {
		this.target = target;
		this.type = type;
	}
	
	public Expression getTarget() {
		return target;
	}
	
	public Type getType() {
		return type;
	}

	@Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		TypeAssertion that = (TypeAssertion) o;
		return Objects.equals(target, that.target) &&
				Objects.equals(type, that.type);
	}

	@Override
	public int hashCode() {

		return Objects.hash(target, type);
	}
}
