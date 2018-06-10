package pgo.model.golang;

import java.util.Objects;

public class Index extends Expression {
	
	Expression target;
	Expression index;
	
	public Index(Expression target, Expression index) {
		this.target = target;
		this.index = index;
	}
	
	public Expression getTarget() {
		return target;
	}
	
	public Expression getIndex() {
		return index;
	}

	@Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		Index index1 = (Index) o;
		return Objects.equals(target, index1.target) &&
				Objects.equals(index, index1.index);
	}

	@Override
	public int hashCode() {

		return Objects.hash(target, index);
	}
}
