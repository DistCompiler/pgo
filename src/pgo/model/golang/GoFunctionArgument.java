package pgo.model.golang;

import pgo.model.golang.type.GoType;

import java.util.Objects;

public class GoFunctionArgument extends GoNode {
	
	private String name;
	private GoType type;

	public GoFunctionArgument(String name, GoType type) {
		this.name = name;
		this.type = type;
	}

	public String getName() {
		return name;
	}

	public GoType getType() {
		return type;
	}
	
	@Override
	public <T, E extends Throwable> T accept(GoNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoFunctionArgument that = (GoFunctionArgument) o;
		return Objects.equals(name, that.name) &&
				Objects.equals(type, that.type);
	}

	@Override
	public int hashCode() {

		return Objects.hash(name, type);
	}
}
