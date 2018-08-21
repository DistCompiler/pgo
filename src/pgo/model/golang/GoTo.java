package pgo.model.golang;

import java.util.Objects;

/**
 * A PlusCalGoto in pluscal and go
 *
 */
public class GoTo extends GoStatement {
	// the to label location
	private GoLabelName to;

	public GoTo(GoLabelName to) {
		this.to = to;
	}

	public GoLabelName getTo() {
		return to;
	}
	
	@Override
	public <T, E extends Throwable> T accept(GoStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoTo goTo = (GoTo) o;
		return Objects.equals(to, goTo.to);
	}

	@Override
	public int hashCode() {

		return Objects.hash(to);
	}
}
