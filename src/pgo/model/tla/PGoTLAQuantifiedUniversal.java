package pgo.model.tla;

import java.util.List;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

/**
 * 
 * TLA AST Node:
 * 
 * \A a, b, c : <expr>
 *
 */
public class PGoTLAQuantifiedUniversal extends PGoTLAExpression {

	private List<PGoTLAQuantifierBound> ids;
	private PGoTLAExpression body;

	public PGoTLAQuantifiedUniversal(List<PGoTLAQuantifierBound> ids, PGoTLAExpression body, int line) {
		super(line);
		this.ids = ids;
		this.body = body;
	}
	
	public List<PGoTLAQuantifierBound> getIds(){
		return ids;
	}
	
	public PGoTLAExpression getBody() {
		return body;
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
