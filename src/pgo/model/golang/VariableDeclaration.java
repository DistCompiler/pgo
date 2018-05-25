package pgo.model.golang;

public class VariableDeclaration extends Declaration {

	private String name;
	private Expression value;

	public VariableDeclaration(String name, Expression value) {
		this.name = name;
		this.value = value;
	}

	public String getName() {
		return name;
	}

	public Expression getValue() {
		return value;
	}

	@Override
	public <T, E extends Throwable> T accept(DeclarationVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
