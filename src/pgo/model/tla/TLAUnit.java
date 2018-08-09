package pgo.model.tla;

import pgo.util.SourceLocation;

public abstract class TLAUnit extends TLANode {
	
	public TLAUnit(SourceLocation location) {
		super(location);
	}
	
	@Override
	public <T, E extends Throwable> T accept(TLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	@Override
	public abstract TLAUnit copy();
	
	public abstract <T, E extends Throwable> T accept(TLAUnitVisitor<T, E> v) throws E;

}
