package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents a slice.
 */
public class SliceType extends SimpleContainerType {
	public SliceType(Type elementType, List<Origin> origins) {
		super(elementType, origins);
	}

	@Override
	public int hashCode() {
		return super.hashCode() * 17 + 7;
	}

	@Override
	public boolean equals(Object p) {
		if (!(p instanceof SliceType)) {
			return false;
		}
		return super.equals(p);
	}

	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
