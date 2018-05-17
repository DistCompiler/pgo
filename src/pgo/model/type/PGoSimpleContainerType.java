package pgo.model.type;

import java.util.Set;

/**
 * Contains overloaded methods for a container type with only one element type, for convenience.
 */
public abstract class PGoSimpleContainerType extends PGoType {
	protected PGoType elementType;

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
	public boolean contains(PGoTypeVariable v) {
		return elementType.contains(v);
	}

	@Override
	public boolean containsVariables() {
		return elementType.containsVariables();
	}

	@Override
	public void collectVariables(Set<PGoTypeVariable> vars) {
		elementType.collectVariables(vars);
	}
}
