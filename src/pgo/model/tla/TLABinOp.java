package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

/**
 * 
 * AST PlusCalNode:
 * 
 * lhs <op> rhs
 * 
 */
public class TLABinOp extends TLAExpression {

	private TLAExpression lhs;
	private TLAExpression rhs;
	private TLASymbol op;
	private List<TLAGeneralIdentifierPart> prefix;
	
	public TLABinOp(SourceLocation location, TLASymbol op, List<TLAGeneralIdentifierPart> prefix, TLAExpression lhs, TLAExpression rhs) {
		super(location);
		this.lhs = lhs;
		this.rhs = rhs;
		this.op = op;
		this.prefix = prefix;
	}
	
	@Override
	public TLABinOp copy() {
		return new TLABinOp(getLocation(), op, prefix.stream().map(TLAGeneralIdentifierPart::copy).collect(Collectors.toList()), lhs.copy(), rhs.copy());
	}
	
	public TLASymbol getOperation() {
		return op;
	}
	
	public TLAExpression getLHS() {
		return lhs;
	}
	
	public TLAExpression getRHS() {
		return rhs;
	}
	
	public List<TLAGeneralIdentifierPart> getPrefix(){
		return prefix;
	}

	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((lhs == null) ? 0 : lhs.hashCode());
		result = prime * result + ((op == null) ? 0 : op.hashCode());
		result = prime * result + ((prefix == null) ? 0 : prefix.hashCode());
		result = prime * result + ((rhs == null) ? 0 : rhs.hashCode());
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
		TLABinOp other = (TLABinOp) obj;
		if (lhs == null) {
			if (other.lhs != null)
				return false;
		} else if (!lhs.equals(other.lhs))
			return false;
		if (op == null) {
			if (other.op != null)
				return false;
		} else if (!op.equals(other.op))
			return false;
		if (prefix == null) {
			if (other.prefix != null)
				return false;
		} else if (!prefix.equals(other.prefix))
			return false;
		if (rhs == null) {
			if (other.rhs != null)
				return false;
		} else if (!rhs.equals(other.rhs))
			return false;
		return true;
	}

}
