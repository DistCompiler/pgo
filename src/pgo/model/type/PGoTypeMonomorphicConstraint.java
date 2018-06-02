package pgo.model.type;

import pgo.util.DerivedVisitor;
import pgo.util.Origin;

import java.util.Collections;
import java.util.List;

public class PGoTypeMonomorphicConstraint extends PGoTypeConstraint {
	private PGoTypeEqualityConstraint equalityConstraint;

	public PGoTypeMonomorphicConstraint(Origin origin, PGoType lhs, PGoType rhs) {
		this(Collections.singletonList(origin), new PGoTypeEqualityConstraint(lhs, rhs));
	}

	public PGoTypeMonomorphicConstraint(List<Origin> origins, PGoTypeEqualityConstraint equalityConstraint) {
		origins.forEach(this::addOrigin);
		this.equalityConstraint = equalityConstraint;
	}

	public PGoType getLhs() {
		return equalityConstraint.getLhs();
	}

	public PGoType getRhs() {
		return equalityConstraint.getRhs();
	}

	@Override
	public <T, E extends Throwable> T accept(DerivedVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public PGoTypeMonomorphicConstraint copy() {
		return this;
	}

	@Override
	public String toString() {
		return getLhs().toString() + " = " + getRhs().toString();
	}
}
