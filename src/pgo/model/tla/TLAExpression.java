package pgo.model.tla;

import pgo.util.SourceLocation;

/**
 * Base TLA GoExpression representation
 *
 */
public abstract class TLAExpression extends TLANode {

	public TLAExpression(SourceLocation location) {
		super(location);
	}
	
	@Override
	public abstract TLAExpression copy();
	
	@Override
	public <T, E extends Throwable> T accept(TLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public abstract <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E;

}
