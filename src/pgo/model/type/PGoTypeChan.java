package pgo.model.type;

import pgo.errors.IssueContext;

import java.util.Map;

/**
 * Represents a channel.
 */
public class PGoTypeChan extends PGoSimpleContainerType {
	public PGoTypeChan(PGoType elementType) {
		this.elementType = elementType;
	}

	@Override
	public boolean equals(Object p) {
		if (!(p instanceof PGoTypeChan)) {
			return false;
		}
		return super.equals(p);
	}

	@Override
	public PGoType substitute(Map<PGoTypeVariable, PGoType> mapping) {
		return new PGoTypeChan(elementType.substitute(mapping));
	}

	@Override
	public PGoType realize(IssueContext ctx) {
		return new PGoTypeChan(elementType.realize(ctx));
	}

	@Override
	public String toTypeName() {
		return "Chan[" + elementType.toTypeName() + "]";
	}

	@Override
	public String toGo() {
		return "chan " + elementType.toGo();
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
