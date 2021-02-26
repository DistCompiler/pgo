package pgo.model.tla;

import pgo.util.SourceLocation;

public class TLACaseArm extends TLANode {
	
	private final TLAExpression cond;
	private final TLAExpression result;

	public TLACaseArm(SourceLocation location, TLAExpression cond, TLAExpression result) {
		super(location);
		this.cond = cond;
		this.result = result;
	}
	
	@Override
	public TLACaseArm copy() {
		return new TLACaseArm(getLocation(), cond.copy(), result.copy());
	}
	
	public TLAExpression getCondition() {
		return cond;
	}
	
	public TLAExpression getResult() {
		return result;
	}
	
	@Override
	public <T, E extends Throwable> T accept(TLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((cond == null) ? 0 : cond.hashCode());
		result = prime * result + ((this.result == null) ? 0 : this.result.hashCode());
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
		TLACaseArm other = (TLACaseArm) obj;
		if (cond == null) {
			if (other.cond != null)
				return false;
		} else if (!cond.equals(other.cond))
			return false;
		if (result == null) {
			return other.result == null;
		} else return result.equals(other.result);
	}
	
}
