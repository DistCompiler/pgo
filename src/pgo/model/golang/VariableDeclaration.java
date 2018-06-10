package pgo.model.golang;

import java.util.Objects;

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

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		VariableDeclaration that = (VariableDeclaration) o;
		return Objects.equals(name, that.name) &&
				Objects.equals(type, that.type) &&
				Objects.equals(value, that.value);
	}

	@Override
	public int hashCode() {

		return Objects.hash(name, type, value);
	}
}
