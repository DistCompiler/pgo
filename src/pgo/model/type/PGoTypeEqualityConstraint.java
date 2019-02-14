package pgo.model.type;

/**
 * A plain old Java object representing an equality constraint.
 */
public class PGoTypeEqualityConstraint {
	private PGoType lhs;
	private PGoType rhs;

	public PGoTypeEqualityConstraint(PGoType lhs, PGoType rhs) {
		this.lhs = lhs;
		this.rhs = rhs;
	}

	public PGoType getLhs() {
		return lhs;
	}

	public PGoType getRhs() {
		return rhs;
	}

	public PGoTypeEqualityConstraint copy() {
		PGoTypeCopyVisitor visitor = new PGoTypeCopyVisitor();
		return new PGoTypeEqualityConstraint(lhs.accept(visitor), rhs.accept(visitor));
	}
}
