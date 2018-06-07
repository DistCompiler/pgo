package pgo.model.golang;

import java.util.Objects;

public class Make extends Expression {

	private Type type;
	private Expression size;
	private Expression capacity;

	public Make(Type type, Expression size, Expression capacity) {
		this.type = type;
		this.size = size;
		this.capacity = capacity;
	}

	public Type getType() {
		return type;
	}

	public Expression getSize() {
		return size;
	}

	public Expression getCapacity() {
		return capacity;
	}

	@Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		Make make = (Make) o;
		return Objects.equals(type, make.type) &&
				Objects.equals(size, make.size) &&
				Objects.equals(capacity, make.capacity);
	}

	@Override
	public int hashCode() {

		return Objects.hash(type, size, capacity);
	}
}
