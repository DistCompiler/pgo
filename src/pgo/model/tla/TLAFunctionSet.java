package pgo.model.tla;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST PlusCalNode:
 * 
 * [ <expr> -> <expr> ]
 * 
 * PlusCalWhile not required at the parsing level, each expr must result in a set.
 * Defines the set of all functions having this signature.
 *
 */
public class TLAFunctionSet extends TLAExpression {

	private TLAExpression from;
	private TLAExpression to;

	public TLAFunctionSet(SourceLocation location, TLAExpression from, TLAExpression to) {
		super(location);
		this.from = from;
		this.to = to;
	}
	
	@Override
	public TLAFunctionSet copy() {
		return new TLAFunctionSet(getLocation(), from.copy(), to.copy());
	}
	
	public TLAExpression getFrom() {
		return from;
	}
	
	public TLAExpression getTo() {
		return to;
	}
	
	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((from == null) ? 0 : from.hashCode());
		result = prime * result + ((to == null) ? 0 : to.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		TLAFunctionSet other = (TLAFunctionSet) obj;
		if (from == null) {
			if (other.from != null)
				return false;
		} else if (!from.equals(other.from))
			return false;
		if (to == null) {
			return other.to == null;
		} else return to.equals(other.to);
	}

}
