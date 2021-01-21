package pgo.model.golang;

import java.util.Objects;

public class GoVariableName extends GoExpression {
	
	private final String name;
	
	public GoVariableName(String name) {
		this.name = name;
	}
	
	public String getName() {
		return name;
	}
	
	@Override
	public <T, E extends Throwable> T accept(GoExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoVariableName that = (GoVariableName) o;
		return Objects.equals(name, that.name);
	}

	@Override
	public int hashCode() {

		return Objects.hash(name);
	}
}
