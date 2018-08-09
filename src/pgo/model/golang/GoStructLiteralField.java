package pgo.model.golang;

import java.util.Objects;

public class GoStructLiteralField extends GoNode {

	private String name;
	private GoExpression value;

	public GoStructLiteralField(String name, GoExpression value){
		this.name = name;
		this.value = value;
	}

	public String getName() {
		return name;
	}

	public GoExpression getValue() {
		return value;
	}

	@Override
	public <T, E extends Throwable> T accept(GoNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoStructLiteralField that = (GoStructLiteralField) o;
		return Objects.equals(name, that.name) &&
				Objects.equals(value, that.value);
	}

	@Override
	public int hashCode() {

		return Objects.hash(name, value);
	}
}
