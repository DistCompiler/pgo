package pgo.model.type;

import pgo.errors.IssueContext;
import pgo.util.Origin;

import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Contains overloaded methods for a primitive type, for convenience.
 */
public abstract class PGoPrimitiveType extends PGoType {
	public PGoPrimitiveType(Origin... origins) {
		super(origins);
	}

	public PGoPrimitiveType(List<Origin> origins) {
		super(origins);
	}

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
	public PGoType realize(IssueContext ctx) {
		return this;
	}
}
