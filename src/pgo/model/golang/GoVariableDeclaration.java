package pgo.model.golang;

import pgo.model.golang.type.GoType;

import java.util.Objects;

public class GoVariableDeclaration extends GoDeclaration {

	private final String name;
	private final GoType type;
	private final GoExpression value;

	public GoVariableDeclaration(String name, GoType type, GoExpression value) {
		this.name = name;
		this.type = type;
		this.value = value;
	}

	public String getName() {
		return name;
	}
	
	public GoType getType() {
		return type;
	}

	public GoExpression getValue() {
		return value;
	}

	@Override
	public <T, E extends Throwable> T accept(GoDeclarationVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoVariableDeclaration that = (GoVariableDeclaration) o;
		return Objects.equals(name, that.name) &&
				Objects.equals(type, that.type) &&
				Objects.equals(value, that.value);
	}

	@Override
	public int hashCode() {

		return Objects.hash(name, type, value);
	}
}
