package pgo.model.tla;

import java.util.List;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

/**
 * 
 * AST Node:
 * 
 * lhs <op> rhs
 * 
 */
public class PGoTLABinOp extends PGoTLAExpression {

	private PGoTLAExpression lhs;
	private PGoTLAExpression rhs;
	private String op;
	private List<PGoTLAGeneralIdentifierPart> prefix;
	
	public PGoTLABinOp(int line, String op, List<PGoTLAGeneralIdentifierPart> prefix, PGoTLAExpression lhs, PGoTLAExpression rhs) {
		super(line);
		this.lhs = lhs;
		this.rhs = rhs;
		this.op = op;
		this.prefix = prefix;
	}
	
	public String getOperation() {
		return op;
	}
	
	public PGoTLAExpression getLHS() {
		return lhs;
	}
	
	public PGoTLAExpression getRHS() {
		return rhs;
	}

	@Override
	public String toString() {
		return "PGoTLABinOp [lhs=" + lhs + ", rhs=" + rhs + ", op=" + op + ", getLine()=" + getLine() + "]";
	}

	@Override
	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		throw new RuntimeException("convert unimplemented");
	}

	@Override
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		throw new RuntimeException("inferType unimplemented");
	}

	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
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
		PGoTLABinOp other = (PGoTLABinOp) obj;
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
