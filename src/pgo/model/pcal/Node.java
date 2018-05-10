package pgo.model.pcal;

import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

public abstract class Node extends SourceLocatable {
	
	SourceLocation location;
	
	public Node(SourceLocation location) {
		this.location = location;
	}

	@Override
	public SourceLocation getLocation() {
		return location;
	}
	
	@Override
	public abstract int hashCode();

	@Override
	public abstract boolean equals(Object obj);

}
