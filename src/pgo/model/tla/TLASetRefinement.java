package pgo.model.tla;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST PlusCalNode:
 * 
 * { a \in <expr> : <expr> }
 * { <<a, b, c>> \in <expr> : <expr> }
 *
 */
public class TLASetRefinement extends TLAExpression {

	private TLAIdentifierOrTuple ident;
	private TLAExpression from;
	private TLAExpression when;

	public TLASetRefinement(SourceLocation location, TLAIdentifierOrTuple ident, TLAExpression from, TLAExpression when) {
		super(location);
		this.ident = ident;
		this.from = from;
		this.when = when;
	}
	
	@Override
	public TLASetRefinement copy() {
		return new TLASetRefinement(getLocation(), ident.copy(), from.copy(), when.copy());
	}
	
	public TLAIdentifierOrTuple getIdent() {
		return ident;
	}
	
	public TLAExpression getFrom() {
		return from;
	}

	public TLAExpression getWhen() {
		return when;
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
		result = prime * result + ((ident == null) ? 0 : ident.hashCode());
		result = prime * result + ((when == null) ? 0 : when.hashCode());
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
		TLASetRefinement other = (TLASetRefinement) obj;
		if (from == null) {
			if (other.from != null)
				return false;
		} else if (!from.equals(other.from))
			return false;
		if (ident == null) {
			if (other.ident != null)
				return false;
		} else if (!ident.equals(other.ident))
			return false;
		if (when == null) {
			return other.when == null;
		} else return when.equals(other.when);
	}

}
