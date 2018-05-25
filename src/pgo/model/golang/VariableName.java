package pgo.model.golang;

public class VariableName extends Expression {
	
	private String name;
	
	public VariableName(String name) {
		this.name = name;
	}
	
	public String getName() {
		return name;
	}
	
	@Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

}
