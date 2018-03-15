package pgo.model.tla;

import java.util.List;
import java.util.Map;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

public class PGoTLALet extends PGoTLAExpression {

	private List<PGoTLAOperator> operators;
	private Map<String, List<PGoTLAFunction>> functions;
	private PGoTLAExpression body;

	public PGoTLALet(List<PGoTLAOperator> operators, Map<String, List<PGoTLAFunction>> functions, PGoTLAExpression body, int line) {
		super(line);
		this.operators = operators;
		this.functions = functions;
		this.body = body;
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
