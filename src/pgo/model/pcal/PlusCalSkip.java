package pgo.model.pcal;

import pgo.util.SourceLocation;

public class PlusCalSkip extends PlusCalStatement {

	public PlusCalSkip(SourceLocation location) {
		super(location);
	}
	
	@Override
	public PlusCalSkip copy() {
		return new PlusCalSkip(getLocation());
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
	public boolean equals(Object obj) {
		return obj != null && obj instanceof PlusCalSkip;
	}

}
