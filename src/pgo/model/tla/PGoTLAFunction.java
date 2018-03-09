package pgo.model.tla;

import java.util.List;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

public class PGoTLAFunction extends PGoTLAExpression {

	private List<PGoTLAQuantifierBound> args;
	private PGoTLAExpression body;

	public PGoTLAFunction(List<PGoTLAQuantifierBound> args, PGoTLAExpression body, int line) {
		super(line);
		this.args = args;
		this.body = body;
	}
	
	public List<PGoTLAQuantifierBound> getArguments(){
		return args;
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
