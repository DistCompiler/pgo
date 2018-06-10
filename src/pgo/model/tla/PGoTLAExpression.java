package pgo.model.tla;

import pgo.util.SourceLocation;

/**
 * Base TLA Expression representation
 *
 */
public abstract class PGoTLAExpression extends PGoTLANode {

	public PGoTLAExpression(SourceLocation location) {
		super(location);
	}
	
	@Override
	public abstract PGoTLAExpression copy();
	
	@Override
	public <T, E extends Throwable> T accept(PGoTLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public abstract <T, E extends Throwable> T accept(PGoTLAExpressionVisitor<T, E> v) throws E;

}
