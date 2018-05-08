package pgo.model.golang;

public class Dot extends Expression {
	
	Expression lhs;
	String name;
	
	public Dot(Expression lhs, String name) {
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
	public <T> T accept(Visitor<T> visitor) {
		return visitor.visit(this);
	}

}
