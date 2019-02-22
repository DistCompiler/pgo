package pgo.model.type;

/**
 * A plain old Java object representing an equality constraint.
 */
public class PGoTypeEqualityConstraint extends PGoTypeBasicConstraint {
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

	@Override
	public PGoTypeEqualityConstraint copy() {
		PGoTypeCopyVisitor visitor = new PGoTypeCopyVisitor();
		return new PGoTypeEqualityConstraint(lhs.accept(visitor), rhs.accept(visitor));
	}

	@Override
	public String toString() {
		return lhs.toString() + " = " + rhs.toString();
	}
}
