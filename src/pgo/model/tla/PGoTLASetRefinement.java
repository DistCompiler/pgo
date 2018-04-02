package pgo.model.tla;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

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

	public PGoTLASetRefinement(PGoTLAIdentifierOrTuple ident, PGoTLAExpression from, PGoTLAExpression when, int line) {
		super(line);
		this.ident = ident;
		this.from = from;
		this.when = when;
	}
	
	public PGoTLAIdentifierOrTuple getIdent() {
		return ident;
	}
	
	public PGoTLAExpression getFrom() {
		return from;
	}
	
	@Override
	public String toString() {
		return "PGoTLASetRefinement [ident=" + ident + ", from=" + from + ", when=" + when + "]";
	}

	public PGoTLAExpression getWhen() {
		return when;
	}

	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		return v.visit(this);
	}

	@Override
	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		throw new RuntimeException("convert not implemented");
	}

	@Override
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		throw new RuntimeException("inferType not implemented");
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
