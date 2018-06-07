package pgo.model.golang;

import java.util.Objects;

public class SliceOperator extends Expression {
	
	Expression target;
	Expression low;
	Expression high;
	Expression max;

	public SliceOperator(Expression target, Expression low, Expression high, Expression max) {
		this.target = target;
		this.low = low;
		this.high = high;
		this.max = max;
	}
	
	public Expression getTarget() {
		return target;
	}
	
	public Expression getLow() {
		return low;
	}
	
	public Expression getHigh() {
		return high;
	}
	
	public Expression getMax() {
		return max;
	}

	@Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		SliceOperator that = (SliceOperator) o;
		return Objects.equals(target, that.target) &&
				Objects.equals(low, that.low) &&
				Objects.equals(high, that.high) &&
				Objects.equals(max, that.max);
	}

	@Override
	public int hashCode() {

		return Objects.hash(target, low, high, max);
	}
}
