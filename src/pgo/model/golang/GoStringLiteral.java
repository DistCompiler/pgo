package pgo.model.golang;

import java.util.Objects;

public class GoStringLiteral extends GoExpression {
	
	private String value;

	public GoStringLiteral(String value) {
		this.value = value;
	}
	
	public String getValue() {
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
		GoStringLiteral that = (GoStringLiteral) o;
		return Objects.equals(value, that.value);
	}

	@Override
	public int hashCode() {

		return Objects.hash(value);
	}
}
