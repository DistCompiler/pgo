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

}
