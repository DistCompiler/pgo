package pgo.model.type;

import pgo.util.Origin;

import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Contains overloaded methods for a container type with only one element type, for convenience.
 */
public abstract class PGoSimpleContainerType extends PGoType {
	protected PGoType elementType;

	public PGoSimpleContainerType(PGoType elementType, List<Origin> origins) {
		super(origins);
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

	@Override
	public boolean containsVariables() {
		return elementType.containsVariables();
	}

	@Override
	public PGoType substitute(Map<PGoTypeVariable, PGoType> mapping) {
		elementType = elementType.substitute(mapping);
		return this;
	}
}
