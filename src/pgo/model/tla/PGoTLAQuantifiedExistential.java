package pgo.model.tla;

import java.util.List;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

/**
 * 
 * TLA AST Node:
 * 
 * \E a, b, c : <expr>
 *
 */
public class PGoTLAQuantifiedExistential extends PGoTLAExpression {

	private PGoTLAExpression body;
	private List<PGoTLAQuantifierBound> ids;

	public PGoTLAQuantifiedExistential(List<PGoTLAQuantifierBound> ids, PGoTLAExpression body, int line) {
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
	public String toString() {
		return "PGoTLAQuantifiedExistential [body=" + body + ", ids=" + ids + ", getLine()=" + getLine() + "]";
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
