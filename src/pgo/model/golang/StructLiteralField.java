package pgo.model.golang;

import java.util.Objects;

public class StructLiteralField extends Node {

	private String name;
	private Expression value;

	public StructLiteralField(String name, Expression value){
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
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		StructLiteralField that = (StructLiteralField) o;
		return Objects.equals(name, that.name) &&
				Objects.equals(value, that.value);
	}

	@Override
	public int hashCode() {

		return Objects.hash(name, value);
	}
}
