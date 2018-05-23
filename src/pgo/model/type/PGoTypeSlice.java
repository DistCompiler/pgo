package pgo.model.type;

import pgo.errors.IssueContext;

import java.util.Map;

/**
 * Represents a slice.
 */
public class PGoTypeSlice extends PGoSimpleContainerType {
	public PGoTypeSlice(PGoType elementType) {
		this.elementType = elementType;
	}

	@Override
	public boolean equals(Object p) {
		if (!(p instanceof PGoTypeSlice)) {
			return false;
		}
		return super.equals(p);
	}

	@Override
	public PGoType substitute(Map<PGoTypeVariable, PGoType> mapping) {
		return new PGoTypeSlice(elementType.substitute(mapping));
	}

	@Override
	public PGoType realize(IssueContext ctx) {
		return new PGoTypeSlice(elementType.realize(ctx));
	}

	@Override
	public String toTypeName() {
		return "Slice[" + elementType.toTypeName() + "]";
	}

	@Override
	public String toGo() {
		return "[]" + elementType.toGo();
	}
}
