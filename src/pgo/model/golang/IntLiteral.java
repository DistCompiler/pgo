package pgo.model.golang;

public class IntLiteral extends Expression {

	private int value;

	public IntLiteral(int value) {
		this.value = value;
	}
	
	public int getValue() {
		return value;
	}

	@Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

}
