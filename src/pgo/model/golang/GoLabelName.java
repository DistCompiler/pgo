package pgo.model.golang;

import java.util.Objects;

public class GoLabelName extends GoNode {
	
	private String name;

	public GoLabelName(String name) {
		this.name = name;
	}
	
	public String getName() {
		return name;
	}
	
	@Override
	public <T, E extends Throwable> T accept(GoNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoLabelName labelName = (GoLabelName) o;
		return Objects.equals(name, labelName.name);
	}

	@Override
	public int hashCode() {

		return Objects.hash(name);
	}
}
