package pgo.model.pcal;

import pgo.util.SourceLocation;

public abstract class Processes extends Node {
	
	public Processes(SourceLocation location) {
		super(location);
	}
	
	public abstract <T, E extends Throwable> T accept(ProcessesVisitor<T, E> v) throws E;

}
