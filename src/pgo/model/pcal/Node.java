package pgo.model.pcal;

import pgo.scope.UID;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

public abstract class Node extends SourceLocatable {
	
	SourceLocation location;
	UID uid;
	
	public Node(SourceLocation location) {
		this.location = location;
		this.uid = new UID();
		this.uid.addOrigin(this);
	}

	@Override
	public SourceLocation getLocation() {
		return location;
	}
	
	public UID getUID() {
		return uid;
	}
	
	@Override
	public abstract int hashCode();

	@Override
	public abstract boolean equals(Object obj);

}
