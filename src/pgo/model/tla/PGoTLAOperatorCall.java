package pgo.model.tla;

import java.util.List;

import pgo.model.golang.Expression;
import pgo.model.type.PGoType;
import pgo.trans.PGoTransException;

/**
 * 
 * TLA AST Node:
 * 
 * op(<expr>, <expr>, ...)
 *
 */
public class PGoTLAOperatorCall extends PGoTLAExpression {

	private String name;
	private List<PGoTLAExpression> args;
	
	public PGoTLAOperatorCall(int line, String name, List<PGoTLAExpression> args) {
		super(line);
		this.name = name;
		this.args = args;
	}
	
	public String getName() {
		return name;
	}
	
	public List<PGoTLAExpression> getArgs(){
		return args;
	}

	@Override
	public String toString() {
		return "PGoTLAOperatorCall [name=" + name + ", args=" + args + ", getLine()=" + getLine() + "]";
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
