package pgo.model.tla;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

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
	
	public PGoTLAIf(int line, PGoTLAExpression cond, PGoTLAExpression tval, PGoTLAExpression fval) {
		super(line);
		this.cond = cond;
		this.tval = tval;
		this.fval = fval;
	}

	@Override
	public String toString() {
		return "PGoTLAIf [cond=" + cond + ", tval=" + tval + ", fval=" + fval + ", getLine()=" + getLine() + "]";
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
