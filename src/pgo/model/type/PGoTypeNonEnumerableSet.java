package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents a non-enumerable set, e.g. Nat, Int, Real.
 */
public class PGoTypeNonEnumerableSet extends PGoTypeSet {
	public PGoTypeNonEnumerableSet(PGoType elementType, Origin... origins) {
		super(elementType, origins);
	}

	public PGoTypeNonEnumerableSet(PGoType elementType, List<Origin> origins) {
		super(elementType, origins);
	}

	@Override
	public boolean isEnumerable() {
		return false;
	}
}
