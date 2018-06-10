package pgo.model.golang;

import java.util.Objects;

public class LabelName extends Node {
	
	private String name;

	public LabelName(String name) {
		this.name = name;
	}
	
	public String getName() {
		return name;
	}
	
	@Override
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		LabelName labelName = (LabelName) o;
		return Objects.equals(name, labelName.name);
	}

	@Override
	public int hashCode() {

		return Objects.hash(name);
	}
}
