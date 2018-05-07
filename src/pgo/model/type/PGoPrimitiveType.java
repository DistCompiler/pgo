package pgo.model.type;

import java.util.Map;
import java.util.Set;

/**
 * Contains overloaded methods for a primitive type, for convenience.
 */
public abstract class PGoPrimitiveType extends PGoType {
	@Override
	public boolean contains(PGoTypeVariable v) {
		return false;
	}

	@Override
	public boolean containsVariables() {
		return false;
	}

	@Override
	public void collectVariables(Set<PGoTypeVariable> vars) {}

	@Override
	public PGoType substitute(Map<PGoTypeVariable, PGoType> mapping) {
		return this;
	}

	@Override
	public PGoType realize() {
		return this;
	}
}
