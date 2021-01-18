package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.Objects;

public class TLARef extends TLAExpression {
	private final String target;
	private TLADefinitionOne refersTo;

	public TLARef(SourceLocation location, String target) {
		super(location);
		this.target = target;
	}

	public void setRefersTo(TLADefinitionOne refersTo) {
		this.refersTo = refersTo;
	}

	public TLADefinitionOne getRefersTo() {
		return refersTo;
	}

	@Override
	public int hashCode() {
		return Objects.hash(target);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || obj.getClass() != getClass()) {
			return false;
		}
		TLARef that = (TLARef) obj;
		return target.equals(that.target);
	}

	@Override
	public TLARef copy() {
		return new TLARef(getLocation(), target);
	}

	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public String getTarget() {
		return target;
	}
}
