package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents a channel.
 */
public class PGoTypeChan extends PGoSimpleContainerType {
	public PGoTypeChan(PGoType elementType, List<Origin> origins) {
		super(elementType, origins);
	}

	@Override
	public int hashCode() {
		return super.hashCode() * 17 + 2;
	}

	@Override
	public boolean equals(Object p) {
		if (!(p instanceof PGoTypeChan)) {
			return false;
		}
		return super.equals(p);
	}

	@Override
	public PGoType copy() {
		return new PGoTypeChan(elementType.copy(), getOrigins());
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
