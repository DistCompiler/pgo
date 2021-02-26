package pgo.model.golang;

import java.util.Objects;

public class GoIntLiteral extends GoExpression {

	private final int value;

	public GoIntLiteral(int value) {
		this.value = value;
	}
	
	public int getValue() {
		return value;
	}

	@Override
	public <T, E extends Throwable> T accept(GoExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoIntLiteral that = (GoIntLiteral) o;
		return value == that.value;
	}

	@Override
	public int hashCode() {

		return Objects.hash(value);
	}
}
