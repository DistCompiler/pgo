package pgo.model.golang;

import java.util.Objects;

public class GoIndexExpression extends GoExpression {
	
	GoExpression target;
	GoExpression index;
	
	public GoIndexExpression(GoExpression target, GoExpression index) {
		this.target = target;
		this.index = index;
	}
	
	public GoExpression getTarget() {
		return target;
	}
	
	public GoExpression getIndex() {
		return index;
	}

	@Override
	public <T, E extends Throwable> T accept(GoExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoIndexExpression index1 = (GoIndexExpression) o;
		return Objects.equals(target, index1.target) &&
				Objects.equals(index, index1.index);
	}

	@Override
	public int hashCode() {

		return Objects.hash(target, index);
	}
}
