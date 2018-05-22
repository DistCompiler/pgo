package pgo.model.pcal;

import pgo.util.SourceLocation;

public abstract class Processes extends Node {
	
	public Processes(SourceLocation location) {
		super(location);
	}
	
	@Override
	public abstract Processes copy();
	
	@Override
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E{
		return v.visit(this);
	}
	
	public abstract <T, E extends Throwable> T accept(ProcessesVisitor<T, E> v) throws E;

}
