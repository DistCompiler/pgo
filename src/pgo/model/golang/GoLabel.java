package pgo.model.golang;

import java.util.Objects;

/**
 * A label in GoRoutineStatement. This will be on it's own line
 *
 */
public class GoLabel extends GoStatement {

	private final String name;

	public GoLabel(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	@Override
	public <T, E extends Throwable> T accept(GoStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoLabel label = (GoLabel) o;
		return Objects.equals(name, label.name);
	}

	@Override
	public int hashCode() {

		return Objects.hash(name);
	}
}
