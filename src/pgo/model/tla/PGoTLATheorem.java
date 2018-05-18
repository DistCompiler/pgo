package pgo.model.tla;

import pgo.util.SourceLocation;

public class PGoTLATheorem extends PGoTLAUnit {
	
	private PGoTLAExpression theorem;

	public PGoTLATheorem(SourceLocation location, PGoTLAExpression theorem) {
		super(location);
		this.theorem = theorem;
	}
	
	@Override
	public PGoTLATheorem copy() {
		return new PGoTLATheorem(getLocation(), theorem.copy());
	}

	public PGoTLAExpression getTheorem() {
		return theorem;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTLAUnitVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((theorem == null) ? 0 : theorem.hashCode());
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
		PGoTLATheorem other = (PGoTLATheorem) obj;
		if (theorem == null) {
			if (other.theorem != null)
				return false;
		} else if (!theorem.equals(other.theorem))
			return false;
		return true;
	}

}
