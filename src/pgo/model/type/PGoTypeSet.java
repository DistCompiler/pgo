package pgo.model.type;

import pgo.errors.IssueContext;

import java.util.Map;

/**
 * Represents a set.
 */
public class PGoTypeSet extends PGoSimpleContainerType {
	public PGoTypeSet(PGoType elementType) {
		this.elementType = elementType;
	}

	@Override
	public boolean equals(Object p) {
		if (!(p instanceof PGoTypeSet)) {
			return false;
		}
		return super.equals(p);
	}

	@Override
	public PGoType substitute(Map<PGoTypeVariable, PGoType> mapping) {
		return new PGoTypeSet(elementType.substitute(mapping));
	}

	@Override
	public PGoType realize(IssueContext ctx) {
		return new PGoTypeSet(elementType.realize(ctx));
	}

	@Override
	public String toTypeName() {
		return "Set[" + elementType.toTypeName() + "]";
	}

	@Override
	public String toGo() {
		return "datatypes.Set";
	}
}
