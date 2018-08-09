package pgo.model.golang;

import java.util.Objects;

public class GoSliceOperator extends GoExpression {
	
	GoExpression target;
	GoExpression low;
	GoExpression high;
	GoExpression max;

	public GoSliceOperator(GoExpression target, GoExpression low, GoExpression high, GoExpression max) {
		this.target = target;
		this.low = low;
		this.high = high;
		this.max = max;
	}
	
	public GoExpression getTarget() {
		return target;
	}
	
	public GoExpression getLow() {
		return low;
	}
	
	public GoExpression getHigh() {
		return high;
	}
	
	public GoExpression getMax() {
		return max;
	}

	@Override
	public <T, E extends Throwable> T accept(GoExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoSliceOperator that = (GoSliceOperator) o;
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
