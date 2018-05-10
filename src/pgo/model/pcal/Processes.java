package pgo.model.pcal;

import pgo.util.SourceLocation;

public abstract class Processes extends Node {
	
	public Processes(SourceLocation location) {
		super(location);
	}

	public abstract class Visitor<T>{

		public abstract T visit(SingleProcess singleProcess);
		public abstract T visit(MultiProcess multiProcess);
		
	}
	
	public abstract <T> T accept(Visitor<T> v);

}
