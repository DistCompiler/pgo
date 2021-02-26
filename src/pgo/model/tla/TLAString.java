package pgo.model.tla;

import pgo.util.SourceLocation;

/**
 * Represents a TLA token string
 * 
 */
public class TLAString extends TLAExpression {

	private final String value;

	public TLAString(SourceLocation location, String value) {
		super(location);
		this.value = value;
	}
	
	@Override
	public TLAString copy() {
		return new TLAString(getLocation(), value);
	}

	public String getValue() {
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
		result = prime * result + ((value == null) ? 0 : value.hashCode());
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
		TLAString other = (TLAString) obj;
		if (value == null) {
			return other.value == null;
		} else return value.equals(other.value);
	}
	
}
