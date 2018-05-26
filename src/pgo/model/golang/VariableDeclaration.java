package pgo.model.golang;

public class VariableDeclaration extends Declaration {

	private String name;
	private Type type;
	private Expression value;

	public VariableDeclaration(String name, Type type, Expression value) {
		this.name = name;
		this.type = type;
		this.value = value;
	}

	public String getName() {
		return name;
	}
	
	public Type getType() {
		return type;
	}

	public Expression getValue() {
		return value;
	}

	@Override
	public <T, E extends Throwable> T accept(DeclarationVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
