package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents a channel.
 */
public class PGoTypeChan extends PGoSimpleContainerType {
	public PGoTypeChan(PGoType elementType, Origin... origins) {
		super(elementType, origins);
	}

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
	public String toGo() {
		return "chan " + elementType.toGo();
	}
}
