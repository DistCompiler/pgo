package pgo.model.tla;

import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

/**
 * 
 * The base class for any TLA AST node. Usually too vague to be useful,
 * but can be useful in error reporting as it defines every TLA AST node
 * as knowing their source file location.
 *
 */
public abstract class PGoTLANode extends SourceLocatable {
	SourceLocation location;
	
	public PGoTLANode(SourceLocation location) {
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
