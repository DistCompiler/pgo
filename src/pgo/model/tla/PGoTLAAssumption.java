package pgo.model.tla;

import pgo.util.SourceLocation;

public class PGoTLAAssumption extends PGoTLAUnit {
	
	PGoTLAExpression assumption;

	public PGoTLAAssumption(SourceLocation location, PGoTLAExpression assumption) {
		super(location);
		this.assumption = assumption;
	}

	public PGoTLAExpression getAssumption() {
		return assumption;
	}

	@Override
	public <T> T accept(Visitor<T> v) {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((assumption == null) ? 0 : assumption.hashCode());
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
		PGoTLAAssumption other = (PGoTLAAssumption) obj;
		if (assumption == null) {
			if (other.assumption != null)
				return false;
		} else if (!assumption.equals(other.assumption))
			return false;
		return true;
	}

}
