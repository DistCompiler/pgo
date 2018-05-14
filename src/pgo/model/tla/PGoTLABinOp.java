package pgo.model.tla;

import pgo.model.golang.Expression;
import pgo.model.type.PGoType;
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
	
	public PGoTLABinOp(int line, String op, PGoTLAExpression lhs, PGoTLAExpression rhs) {
		super(line);
		this.lhs = lhs;
		this.rhs = rhs;
		this.op = op;
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

}
