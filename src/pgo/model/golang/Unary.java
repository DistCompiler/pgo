package pgo.model.golang;

public class Unary extends Expression {
	
	Expression target;
	private Operation op;
	
	public static enum Operation {
		POS,
		NEG,
		NOT,
		COMPLEMENT,
		DEREF,
		ADDR,
		RECV,
	}
	
	public Unary(Operation op, Expression target) {
		this.op = op;
		this.target = target;
	}
	
	public Operation getOperation() {
		return op;
	}
	
	public Expression getTarget() {
		return target;
	}

	@Override
	public <T> T accept(Visitor<T> visitor) {
		return visitor.visit(this);
	}

}