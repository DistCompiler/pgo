package pgo.model.golang;

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
	public <T> T accept(Visitor<T> visitor) {
		return visitor.visit(this);
	}

}
