package pgo.model.golang;

public class Selector extends Expression {
	
	Expression lhs;
	String name;
	
	public Selector(Expression lhs, String name) {
		this.lhs = lhs;
		this.name = name;
	}
	
	public Expression getLHS() {
		return lhs;
	}
	
	public String getName() {
		return name;
	}

	@Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

}
