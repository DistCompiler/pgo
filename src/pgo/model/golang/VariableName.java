package pgo.model.golang;

public class VariableName extends Expression {
	
	String name;
	Type type;
	
	public VariableName(String name, Type type) {
		this.name = name;
		this.type = type;
	}
	
	public String getName() {
		return name;
	}
	
	public Type getType() {
		return type;
	}
	
	@Override
	public <T> T accept(Expression.Visitor<T> v) {
		return v.visit(this);
	}

}
