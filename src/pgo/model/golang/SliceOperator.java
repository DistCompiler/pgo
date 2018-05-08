package pgo.model.golang;

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
	public <T> T accept(Visitor<T> visitor) {
		return visitor.visit(this);
	}

}
