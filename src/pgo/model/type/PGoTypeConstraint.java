package pgo.model.type;

/**
 * Represents a type constraint, along with the line from which this constraint
 * originates.
 */
public class PGoTypeConstraint {
	private PGoType lhs, rhs;

	public PGoTypeConstraint(PGoType lhs, PGoType rhs) {
		this.lhs = lhs;
		this.rhs = rhs;
	}

	public PGoType getLhs() {
		return lhs;
	}

	public PGoType getRhs() {
		return rhs;
	}
}
