package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents a non-enumerable set, e.g. Nat, Int, Real.
 */
public class PGoTypeNonEnumerableSet extends PGoSimpleContainerType {
	public PGoTypeNonEnumerableSet(PGoType elementType, List<Origin> origins) {
		super(elementType, origins);
	}

	@Override
	public boolean equals(Object p) {
		if (!(p instanceof PGoTypeNonEnumerableSet)) {
			return false;
		}
		return super.equals(p);
	}

	@Override
	public PGoType copy() {
		return new PGoTypeNonEnumerableSet(elementType.copy(), getOrigins());
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
