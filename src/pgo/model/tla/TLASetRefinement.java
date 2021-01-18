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
public class TLASetRefinement extends TLAExpression {

	private TLAQuantifierBound binding;
	private TLAExpression when;

	public TLASetRefinement(SourceLocation location, TLAQuantifierBound binding, TLAExpression when) {
		super(location);
		this.binding = binding;
		this.when = when;
	}
	
	@Override
	public TLASetRefinement copy() {
		return new TLASetRefinement(getLocation(), binding.copy(), when.copy());
	}
	
	public TLAQuantifierBound getBinding() {
		return binding;
	}

	public TLAIdentifierOrTuple getIdent() {
		return binding.identifierOrTuple();
	}

	public TLAExpression getFrom() {
		return binding.getSet();
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
		result = prime * result + ((binding == null) ? 0 : binding.hashCode());
		result = prime * result + ((when == null) ? 0 : when.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		TLASetRefinement that = (TLASetRefinement) o;
		return binding.equals(that.binding) && when.equals(that.when);
	}
}
