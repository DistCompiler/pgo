package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Contains overloaded methods for a container type with only one element type, for convenience.
 */
public abstract class SimpleContainerType extends Type {
	protected Type elementType;

	public SimpleContainerType(Type elementType, List<Origin> origins) {
		super(origins);
		this.elementType = elementType;
	}

	void setElementType(Type elementType) {
		this.elementType = elementType;
	}

	public Type getElementType() {
		return elementType;
	}

	@Override
	public int hashCode() {
		return elementType.hashCode();
	}

	@Override
	public boolean equals(Object p) {
		if (!(p instanceof SimpleContainerType)) {
			return false;
		}
		return elementType.equals(((SimpleContainerType) p).elementType);
	}
}
