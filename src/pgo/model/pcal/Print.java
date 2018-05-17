package pgo.model.pcal;

import pgo.model.tla.PGoTLAExpression;
import pgo.util.SourceLocation;

public class Print extends Statement {
	
	PGoTLAExpression value;
	
	public Print(SourceLocation location, PGoTLAExpression value) {
		super(location);
		this.value = value;
	}
	
	public PGoTLAExpression getValue() {
		return value;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
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
		Print other = (Print) obj;
		if (value == null) {
			if (other.value != null)
				return false;
		} else if (!value.equals(other.value))
			return false;
		return true;
	}

}
