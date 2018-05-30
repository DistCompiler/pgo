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
	public boolean equals(Object p) {
		if (!(p instanceof PGoTypeChan)) {
			return false;
		}
		return super.equals(p);
	}

	@Override
	public String toTypeName() {
		return "Chan[" + elementType.toTypeName() + "]";
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
