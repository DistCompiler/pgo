package pgo.model.pcal;

import pgo.util.SourceLocation;

public class PlusCalReturn extends PlusCalStatement {
	public PlusCalReturn(SourceLocation location) {
		super(location);
	}
	
	@Override
	public PlusCalReturn copy() {
		return new PlusCalReturn(getLocation());
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	@Override
	public int hashCode() {
		return 0;
	}
	
	@Override
	public boolean equals(Object other) {
		return other instanceof PlusCalReturn;
	}
}
