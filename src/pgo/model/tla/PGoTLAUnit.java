package pgo.model.tla;

import pgo.util.SourceLocation;

public abstract class PGoTLAUnit extends PGoTLANode {
	
	public PGoTLAUnit(SourceLocation location) {
		super(location);
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public abstract <T, E extends Throwable> T accept(PGoTLAUnitVisitor<T, E> v) throws E;

}
