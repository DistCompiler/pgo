package pgo.model.tla;

import pgo.util.SourceLocation;

/**
 * Represents a tla token for a number
 *
 */
public class PGoTLANumber extends PGoTLAExpression {

	public enum Base {
		DECIMAL,
		BINARY,
		OCTAL,
		HEXADECIMAL
	}

	private String val;
	private Base base;

	public PGoTLANumber(SourceLocation location, String val, Base base) {
		super(location);
		this.val = val;
		this.base = base;
	}
	
	@Override
	public PGoTLANumber copy() {
		return new PGoTLANumber(getLocation(), val, base);
	}

	public String getVal() {
		return val;
	}

	public Base getBase() { return base; }
	
	@Override
	public <T, E extends Throwable> T accept(PGoTLAExpressionVisitor<T, E> v) throws E {
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
		PGoTLANumber other = (PGoTLANumber) obj;
		if (val == null) {
			if (other.val != null)
				return false;
		} else if (!val.equals(other.val))
			return false;
		return true;
	}
}
