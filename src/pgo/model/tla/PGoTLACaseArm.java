package pgo.model.tla;

import pgo.util.SourceLocation;

public class PGoTLACaseArm extends PGoTLANode {
	
	private PGoTLAExpression cond;
	private PGoTLAExpression result;

	public PGoTLACaseArm(SourceLocation location, PGoTLAExpression cond, PGoTLAExpression result) {
		super(location);
		this.cond = cond;
		this.result = result;
	}
	
	public PGoTLAExpression getCondition() {
		return cond;
	}
	
	public PGoTLAExpression getResult() {
		return result;
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
		PGoTLACaseArm other = (PGoTLACaseArm) obj;
		if (cond == null) {
			if (other.cond != null)
				return false;
		} else if (!cond.equals(other.cond))
			return false;
		if (result == null) {
			if (other.result != null)
				return false;
		} else if (!result.equals(other.result))
			return false;
		return true;
	}
	
}
