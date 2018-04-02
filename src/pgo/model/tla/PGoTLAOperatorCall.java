package pgo.model.tla;

import java.util.List;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
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
	private List<PGoTLAGeneralIdentifierPart> prefix;
	
	public PGoTLAOperatorCall(int line, String name, List<PGoTLAGeneralIdentifierPart> prefix, List<PGoTLAExpression> args) {
		super(line);
		this.name = name;
		this.args = args;
		this.prefix = prefix;
	}
	
	public String getName() {
		return name;
	}
	
	public List<PGoTLAExpression> getArgs(){
		return args;
	}
	
	public List<PGoTLAGeneralIdentifierPart> getGeneralIdentifierPrefix(){
		return prefix;
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

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((args == null) ? 0 : args.hashCode());
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((prefix == null) ? 0 : prefix.hashCode());
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
		PGoTLAOperatorCall other = (PGoTLAOperatorCall) obj;
		if (args == null) {
			if (other.args != null)
				return false;
		} else if (!args.equals(other.args))
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (prefix == null) {
			if (other.prefix != null)
				return false;
		} else if (!prefix.equals(other.prefix))
			return false;
		return true;
	}

}
