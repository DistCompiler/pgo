package pgo.model.tla;

import java.util.List;
import java.util.Map;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

public class PGoTLALet extends PGoTLAExpression {

	private Map<String, PGoTLAOperator> operators;
	private Map<String, PGoTLAFunction> functions;
	private PGoTLAExpression body;
	private List<PGoTLAInstance> instances;

	public PGoTLALet(Map<String, PGoTLAOperator> operators, Map<String, PGoTLAFunction> functions, List<PGoTLAInstance> instances, PGoTLAExpression body, int line) {
		super(line);
		this.operators = operators;
		this.functions = functions;
		this.instances = instances;
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
