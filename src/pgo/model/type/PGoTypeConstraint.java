package pgo.model.type;

import pgo.util.Derived;
import pgo.util.DerivedVisitor;
import pgo.util.Origin;

/**
 * Represents a type constraint, along with the line from which this constraint
 * originates.
 */
public class PGoTypeConstraint extends Derived {
	private PGoType lhs, rhs;

	public PGoTypeConstraint(Origin origin, PGoType lhs, PGoType rhs) {
		this.addOrigin(origin);
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
	public <T, E extends Throwable> T accept(DerivedVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
