package pgo.model.type;

import pgo.util.DerivedVisitor;
import pgo.util.Origin;

import java.util.Collections;
import java.util.List;

public class PGoTypeMonomorphicConstraint extends PGoTypeConstraint {
	private PGoTypeBasicConstraint basicConstraint;

	public PGoTypeMonomorphicConstraint(Origin origin, PGoType lhs, PGoType rhs) {
		this(Collections.singletonList(origin), new PGoTypeEqualityConstraint(lhs, rhs));
	}

	public PGoTypeMonomorphicConstraint(Origin origin, PGoTypeAbstractRecord abstractRecord, String fieldName,
	                                    PGoType fieldType) {
		this(Collections.singletonList(origin), new PGoTypeHasFieldConstraint(abstractRecord, fieldName, fieldType));
	}

	public PGoTypeMonomorphicConstraint(Origin origin, PGoTypeRecord concreteRecord, String fieldName,
	                                    PGoType fieldType) {
		this(Collections.singletonList(origin), new PGoTypeHasFieldConstraint(concreteRecord, fieldName, fieldType));
	}

	public PGoTypeMonomorphicConstraint(List<Origin> origins, PGoTypeBasicConstraint basicConstraint) {
		origins.forEach(this::addOrigin);
		this.basicConstraint = basicConstraint;
	}

	public PGoTypeBasicConstraint getBasicConstraint() {
		return basicConstraint;
	}

	@Override
	public <T, E extends Throwable> T accept(DerivedVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public PGoTypeMonomorphicConstraint copy() {
		return new PGoTypeMonomorphicConstraint(getOrigins(), basicConstraint.copy());
	}

	@Override
	public String toString() {
		return basicConstraint.toString();
	}
}
