package pgo.model.golang;

import java.util.Objects;

/**
 * A Goto in pluscal and go
 *
 */
public class GoTo extends Statement {
	// the to label location
	private LabelName to;

	public GoTo(LabelName to) {
		this.to = to;
	}

	public LabelName getTo() {
		return to;
	}
	
	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
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
