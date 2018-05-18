package pgo.model.tla;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST Node:
 * 
 * IF <expr> THEN <expr> ELSE <expr>
 *
 */
public class PGoTLAIf extends PGoTLAExpression {

	private PGoTLAExpression cond;
	private PGoTLAExpression tval;
	private PGoTLAExpression fval;
	
	public PGoTLAIf(SourceLocation location, PGoTLAExpression cond, PGoTLAExpression tval, PGoTLAExpression fval) {
		super(location);
		this.cond = cond;
		this.tval = tval;
		this.fval = fval;
	}
	
	@Override
	public PGoTLAIf copy() {
		return new PGoTLAIf(getLocation(), cond.copy(), tval.copy(), fval.copy());
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public PGoTLAExpression getCond() {
		return cond;
	}

	public PGoTLAExpression getTval() {
		return tval;
	}

	public PGoTLAExpression getFval() {
		return fval;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((cond == null) ? 0 : cond.hashCode());
		result = prime * result + ((fval == null) ? 0 : fval.hashCode());
		result = prime * result + ((tval == null) ? 0 : tval.hashCode());
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
		PGoTLAIf other = (PGoTLAIf) obj;
		if (cond == null) {
			if (other.cond != null)
				return false;
		} else if (!cond.equals(other.cond))
			return false;
		if (fval == null) {
			if (other.fval != null)
				return false;
		} else if (!fval.equals(other.fval))
			return false;
		if (tval == null) {
			if (other.tval != null)
				return false;
		} else if (!tval.equals(other.tval))
			return false;
		return true;
	}

}
