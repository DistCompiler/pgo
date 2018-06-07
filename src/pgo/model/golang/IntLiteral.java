package pgo.model.golang;

import java.util.Objects;

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

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		IntLiteral that = (IntLiteral) o;
		return value == that.value;
	}

	@Override
	public int hashCode() {

		return Objects.hash(value);
	}
}
