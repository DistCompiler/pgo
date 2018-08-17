package pgo.model.pcal;

import pgo.model.tla.TLAExpression;
import pgo.util.SourceLocation;

public class PlusCalAssignmentPair extends PlusCalNode {
	
	private TLAExpression lhs;
	private TLAExpression rhs;

	public PlusCalAssignmentPair(SourceLocation location, TLAExpression lhs, TLAExpression rhs) {
		super(location);
		this.lhs = lhs;
		this.rhs = rhs;
	}

	public TLAExpression getLhs() {
		return lhs;
	}

	public TLAExpression getRhs() {
		return rhs;
	}

	@Override
	public PlusCalAssignmentPair copy() {
		return new PlusCalAssignmentPair(getLocation(), lhs.copy(), rhs.copy());
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((lhs == null) ? 0 : lhs.hashCode());
		result = prime * result + ((rhs == null) ? 0 : rhs.hashCode());
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
		PlusCalAssignmentPair other = (PlusCalAssignmentPair) obj;
		if (lhs == null) {
			if (other.lhs != null)
				return false;
		} else if (!lhs.equals(other.lhs))
			return false;
		if (rhs == null) {
			return other.rhs == null;
		} else return rhs.equals(other.rhs);
	}

}
