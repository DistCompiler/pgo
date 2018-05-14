package pgo.model.tla;

import java.util.List;
import java.util.Map;

import pgo.model.golang.Expression;
import pgo.model.type.PGoType;
import pgo.trans.PGoTransException;

/**
 * 
 * TLA AST Node:
 * 
 * LET op(a, b, c) == <expr>
 * 	   fn[d \in D] == <expr>
 *     e + f == <expr>
 *     g == INSTANCE ...
 * IN
 *     <expr>
 *
 */
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
	
	public List<PGoTLAInstance> getModuleDefinitions(){
		return instances;
	}
	
	public Map<String, PGoTLAOperator> getOperatorDefinitions(){
		return operators;
	}
	
	public Map<String, PGoTLAFunction> getFunctionDefinitions(){
		return functions;
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
