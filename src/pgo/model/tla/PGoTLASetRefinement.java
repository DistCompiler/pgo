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

}
