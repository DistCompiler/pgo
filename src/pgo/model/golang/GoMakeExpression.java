package pgo.model.golang;

import pgo.model.golang.type.GoType;

import java.util.Objects;

public class GoMakeExpression extends GoExpression {

	private final GoType type;
	private final GoExpression size;
	private final GoExpression capacity;

	public GoMakeExpression(GoType type, GoExpression size, GoExpression capacity) {
		this.type = type;
		this.size = size;
		this.capacity = capacity;
	}

	public GoMakeExpression(GoType type, GoExpression size) {
		this(type, size, null);
	}

	public GoType getType() {
		return type;
	}

	public GoExpression getSize() {
		return size;
	}

	public GoExpression getCapacity() {
		return capacity;
	}

	@Override
	public <T, E extends Throwable> T accept(GoExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoMakeExpression make = (GoMakeExpression) o;
		return Objects.equals(type, make.type) &&
				Objects.equals(size, make.size) &&
				Objects.equals(capacity, make.capacity);
	}

	@Override
	public int hashCode() {

		return Objects.hash(type, size, capacity);
	}
}
