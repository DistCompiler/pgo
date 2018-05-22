package pgo.model.pcal;

import pgo.util.SourceLocation;

public abstract class Statement extends Node {
	
	public Statement(SourceLocation location) {
		super(location);
	}
	
	@Override
	public abstract Statement copy();
	
	@Override
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E{
		return v.visit(this);
	}
	
	public abstract <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E;

}
