package pgo.model.tla;

import pgo.util.SourceLocation;

/**
 * Represents a tla token for a number
 *
 */
public class TLANumber extends TLAExpression {

	public enum Base {
		DECIMAL,
		BINARY,
		OCTAL,
		HEXADECIMAL
	}

	private String val;
	private Base base;

	public TLANumber(SourceLocation location, String val, Base base) {
		super(location);
		this.val = val;
		this.base = base;
	}
	
	@Override
	public TLANumber copy() {
		return new TLANumber(getLocation(), val, base);
	}

	public String getVal() {
		return val;
	}

	public Base getBase() { return base; }
	
	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((val == null) ? 0 : val.hashCode());
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
		TLANumber other = (TLANumber) obj;
		if (val == null) {
			return other.val == null;
		} else return val.equals(other.val);
	}
}
