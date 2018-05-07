package pgo.model.type;

/**
 * Represents a type constraint, along with the line from which this constraint
 * originates.
 */
public class PGoTypeConstraint {
	private PGoType lhs, rhs;
	private int line;

	public PGoTypeConstraint(PGoType lhs, PGoType rhs, int line) {
		this.lhs = lhs;
		this.rhs = rhs;
		this.line = line;
	}

	public PGoType getLhs() {
		return lhs;
	}

	public PGoType getRhs() {
		return rhs;
	}

	public int getLine() {
		return line;
	}
}
