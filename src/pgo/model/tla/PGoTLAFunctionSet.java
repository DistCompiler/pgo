package pgo.model.tla;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

/**
 * 
 * TLA AST Node:
 * 
 * [ <expr> -> <expr> ]
 * 
 * While not required at the parsing level, each expr must result in a set.
 * Defines the set of all functions having this signature.
 *
 */
public class PGoTLAFunctionSet extends PGoTLAExpression {

	private PGoTLAExpression from;
	private PGoTLAExpression to;

	public PGoTLAFunctionSet(PGoTLAExpression from, PGoTLAExpression to, int line) {
		super(line);
		this.from = from;
		this.to = to;
	}
	
	public PGoTLAExpression getFrom() {
		return from;
	}
	
	public PGoTLAExpression getTo() {
		return to;
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
		PGoTLAFunctionSet other = (PGoTLAFunctionSet) obj;
		if (from == null) {
			if (other.from != null)
				return false;
		} else if (!from.equals(other.from))
			return false;
		if (to == null) {
			if (other.to != null)
				return false;
		} else if (!to.equals(other.to))
			return false;
		return true;
	}

}
