package pgo.model.pcal;

import pgo.util.SourceLocation;

public abstract class PlusCalStatement extends PlusCalNode {
	public PlusCalStatement(SourceLocation location) {
		super(location);
	}
	
	@Override
	public abstract PlusCalStatement copy();
	
	@Override
	public <T, E extends Throwable> T accept(PlusCalNodeVisitor<T, E> v) throws E{
		return v.visit(this);
	}
	
	public abstract <T, E extends Throwable> T accept(PlusCalStatementVisitor<T, E> v) throws E;
}
