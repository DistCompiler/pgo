package pgo.model.golang;

import java.util.Objects;

/**
 * A label in Go. This will be on it's own line
 *
 */
public class Label extends Statement {

	private String name;

	public Label(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		Label label = (Label) o;
		return Objects.equals(name, label.name);
	}

	@Override
	public int hashCode() {

		return Objects.hash(name);
	}
}
