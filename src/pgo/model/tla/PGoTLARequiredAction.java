package pgo.model.tla;

import pgo.model.golang.Expression;
import pgo.model.type.PGoType;
import pgo.trans.PGoTransException;

/**
 * 
 * TLA AST Node:
 * 
 * << <expr> >>_ <expr>
 *
 */
public class PGoTLARequiredAction extends PGoTLAExpression {

	private PGoTLAExpression body;
	private PGoTLAExpression vars;
	
	public PGoTLARequiredAction(int line, PGoTLAExpression body, PGoTLAExpression vars) {
		super(line);
		this.body = body;
		this.vars = vars;
	}

	@Override
	public String toString() {
		return "PGoTLARequiredAction [body=" + body + ", vars=" + vars + ", getLine()=" + getLine() + "]";
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
