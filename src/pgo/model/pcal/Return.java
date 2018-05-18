package pgo.model.pcal;

import pgo.util.SourceLocation;

public class Return extends Statement {
	
	public Return(SourceLocation location) {
		super(location);
	}
	
	@Override
	public Return copy() {
		return new Return(getLocation());
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	@Override
	public int hashCode() {
		return 0;
	}
	
	@Override
	public boolean equals(Object other) {
		return other != null && other instanceof Return;
	}

}
