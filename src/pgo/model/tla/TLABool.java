package pgo.model.tla;

import pgo.util.SourceLocation;

public class TLABool extends TLAExpression {

	private final boolean value;

	public TLABool(SourceLocation location, boolean value) {
		super(location);
		this.value = value;
	}
	
	@Override
	public TLABool copy() {
		return new TLABool(getLocation(), value);
	}

	public boolean getValue() {
		return value;
	}

	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (value ? 1231 : 1237);
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		TLABool other = (TLABool) obj;
		return value == other.value;
	}
	
}
