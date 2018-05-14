package pgo.model.tla;

import java.util.List;

import pgo.model.golang.Expression;
import pgo.model.type.PGoType;
import pgo.trans.PGoTransException;

/*
 * TLA AST Node:
 * 
 * \E a, b, c : <expr>
 * or
 * \EE a, b, c : <expr>
 * 
 */
public class PGoTLAExistential extends PGoTLAExpression {
	
	private List<String> ids;
	private PGoTLAExpression body;

	public PGoTLAExistential(List<String> ids, PGoTLAExpression body, int line) {
		super(line);
		this.ids = ids;
		this.body = body;
	}
	
	public List<String> getIds(){
		return ids;
	}
	
	public PGoTLAExpression getBody() {
		return body;
	}

	@Override
	public String toString() {
		return "PGoTLAExistential [ids=" + ids + ", body=" + body + "]";
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
