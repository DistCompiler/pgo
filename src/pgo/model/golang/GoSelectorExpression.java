package pgo.model.golang;

import java.util.Objects;

public class GoSelectorExpression extends GoExpression {
	
	GoExpression lhs;
	String name;
	
	public GoSelectorExpression(GoExpression lhs, String name) {
		this.lhs = lhs;
		this.name = name;
	}
	
	public GoExpression getLHS() {
		return lhs;
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
		GoSelectorExpression selector = (GoSelectorExpression) o;
		return Objects.equals(lhs, selector.lhs) &&
				Objects.equals(name, selector.name);
	}

	@Override
	public int hashCode() {

		return Objects.hash(lhs, name);
	}
}
