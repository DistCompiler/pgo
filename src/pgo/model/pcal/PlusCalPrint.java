package pgo.model.pcal;

import pgo.model.tla.TLAExpression;
import pgo.util.SourceLocation;

public class PlusCalPrint extends PlusCalStatement {
	
	private TLAExpression value;
	
	public PlusCalPrint(SourceLocation location, TLAExpression value) {
		super(location);
		this.value = value;
	}
	
	@Override
	public PlusCalPrint copy() {
		return new PlusCalPrint(getLocation(), value.copy());
	}
	
	public TLAExpression getValue() {
		return value;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalStatementVisitor<T, E> v) throws E {
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
		PlusCalPrint other = (PlusCalPrint) obj;
		if (value == null) {
			return other.value == null;
		} else return value.equals(other.value);
	}

}
