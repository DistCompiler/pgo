package pgo.model.tla;

import java.util.List;
import java.util.Map;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
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

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((body == null) ? 0 : body.hashCode());
		result = prime * result + ((functions == null) ? 0 : functions.hashCode());
		result = prime * result + ((instances == null) ? 0 : instances.hashCode());
		result = prime * result + ((operators == null) ? 0 : operators.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		PGoTLALet other = (PGoTLALet) obj;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		if (functions == null) {
			if (other.functions != null)
				return false;
		} else if (!functions.equals(other.functions))
			return false;
		if (instances == null) {
			if (other.instances != null)
				return false;
		} else if (!instances.equals(other.instances))
			return false;
		if (operators == null) {
			if (other.operators != null)
				return false;
		} else if (!operators.equals(other.operators))
			return false;
		return true;
	}

}
