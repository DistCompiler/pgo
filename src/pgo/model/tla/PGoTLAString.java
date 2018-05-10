package pgo.model.tla;

import pgo.util.SourceLocation;

/**
 * Represents a TLA token string
 * 
 */
public class PGoTLAString extends PGoTLAExpression {

	private String value;

	public PGoTLAString(SourceLocation location, String value) {
		super(location);
		this.value = value;
	}

	public String getValue() {
		return value;
	}
	
	@Override
	public <T> T accept(Visitor<T> v) {
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
		PGoTLAString other = (PGoTLAString) obj;
		if (value == null) {
			if (other.value != null)
				return false;
		} else if (!value.equals(other.value))
			return false;
		return true;
	}
	
}
