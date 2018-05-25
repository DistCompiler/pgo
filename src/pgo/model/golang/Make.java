package pgo.model.golang;

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

}
