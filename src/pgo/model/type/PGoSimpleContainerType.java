package pgo.model.type;

import pgo.util.Origin;

import java.util.List;
import java.util.Map;

/**
 * Contains overloaded methods for a container type with only one element type, for convenience.
 */
public abstract class PGoSimpleContainerType extends PGoType {
	protected PGoType elementType;

	public PGoSimpleContainerType(PGoType elementType, List<Origin> origins) {
		super(origins);
		this.elementType = elementType;
	}

	void setElementType(PGoType elementType) {
		this.elementType = elementType;
	}

	public PGoType getElementType() {
		return elementType;
	}

	@Override
	public boolean equals(Object p) {
		if (!(p instanceof PGoSimpleContainerType)) {
			return false;
		}
		return elementType.equals(((PGoSimpleContainerType) p).elementType);
	}
}
