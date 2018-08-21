package pgo.model.pcal;

import pgo.util.SourceLocation;

public abstract class PlusCalProcesses extends PlusCalNode {
	
	public PlusCalProcesses(SourceLocation location) {
		super(location);
	}
	
	@Override
	public abstract PlusCalProcesses copy();
	
	@Override
	public <T, E extends Throwable> T accept(PlusCalNodeVisitor<T, E> v) throws E{
		return v.visit(this);
	}
	
	public abstract <T, E extends Throwable> T accept(PlusCalProcessesVisitor<T, E> v) throws E;

}
