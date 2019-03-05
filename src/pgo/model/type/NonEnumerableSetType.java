package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents a non-enumerable set, e.g. Nat, Int, Real.
 */
public class NonEnumerableSetType extends SimpleContainerType {
	public NonEnumerableSetType(Type elementType, List<Origin> origins) {
		super(elementType, origins);
	}

	@Override
	public int hashCode() {
		return super.hashCode() * 17 + 3;
	}

	@Override
	public boolean equals(Object p) {
		if (!(p instanceof NonEnumerableSetType)) {
			return false;
		}
		return super.equals(p);
	}

	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
