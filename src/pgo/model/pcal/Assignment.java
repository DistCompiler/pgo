package pgo.model.pcal;

import pgo.model.tla.PGoTLAExpression;
import pgo.util.SourceLocation;

public class Assignment extends Statement {
	
	PGoTLAExpression lhs;
	PGoTLAExpression rhs;
	
	public Assignment(SourceLocation location, PGoTLAExpression lhs, PGoTLAExpression rhs) {
		super(location);
		this.lhs = lhs;
		this.rhs = rhs;
	}
	
	public PGoTLAExpression getLHS() {
		return lhs;
	}
	
	public PGoTLAExpression getRHS() {
		return rhs;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
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
		Assignment other = (Assignment) obj;
		if (lhs == null) {
			if (other.lhs != null)
				return false;
		} else if (!lhs.equals(other.lhs))
			return false;
		if (rhs == null) {
			if (other.rhs != null)
				return false;
		} else if (!rhs.equals(other.rhs))
			return false;
		return true;
	}

}
