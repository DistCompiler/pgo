package pgo.model.tla;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST Node:
 * 
 * { a \in <expr> : <expr> }
 * { <<a, b, c>> \in <expr> : <expr> }
 *
 */
public class PGoTLASetRefinement extends PGoTLAExpression {

	private PGoTLAIdentifierOrTuple ident;
	private PGoTLAExpression from;
	private PGoTLAExpression when;

	public PGoTLASetRefinement(SourceLocation location, PGoTLAIdentifierOrTuple ident, PGoTLAExpression from, PGoTLAExpression when) {
		super(location);
		this.ident = ident;
		this.from = from;
		this.when = when;
	}
	
	@Override
	public PGoTLASetRefinement copy() {
		return new PGoTLASetRefinement(getLocation(), ident.copy(), from.copy(), when.copy());
	}
	
	public PGoTLAIdentifierOrTuple getIdent() {
		return ident;
	}
	
	public PGoTLAExpression getFrom() {
		return from;
	}

	public PGoTLAExpression getWhen() {
		return when;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTLAExpressionVisitor<T, E> v) throws E {
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
		PGoTLASetRefinement other = (PGoTLASetRefinement) obj;
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
			if (other.when != null)
				return false;
		} else if (!when.equals(other.when))
			return false;
		return true;
	}

}
