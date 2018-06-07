package pgo.model.golang;

import java.util.Objects;

public class StructTypeField extends Node {
	private String name;
	private Type type;
	
	public StructTypeField(String name, Type type) {
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
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		StructTypeField that = (StructTypeField) o;
		return Objects.equals(name, that.name) &&
				Objects.equals(type, that.type);
	}

	@Override
	public int hashCode() {

		return Objects.hash(name, type);
	}
}
