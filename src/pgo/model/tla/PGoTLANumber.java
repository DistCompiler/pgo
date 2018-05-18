package pgo.model.tla;

import pgo.util.SourceLocation;

/**
 * Represents a tla token for a number
 *
 */
public class PGoTLANumber extends PGoTLAExpression {

	private String val;

	public PGoTLANumber(SourceLocation location, String val) {
		super(location);
		this.val = val;
	}
	
	@Override
	public PGoTLANumber copy() {
		return new PGoTLANumber(getLocation(), val);
	}

	public String getVal() {
		return val;
	}
	
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
