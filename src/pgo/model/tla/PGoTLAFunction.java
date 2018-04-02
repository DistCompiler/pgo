package pgo.model.tla;

import java.util.List;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

/**
 * 
 * TLA AST Node:
 * 
 * [ a \in B, << c, d >> \in E |-> <expr> ]
 *
 */
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
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((args == null) ? 0 : args.hashCode());
		result = prime * result + ((body == null) ? 0 : body.hashCode());
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
		PGoTLAFunction other = (PGoTLAFunction) obj;
		if (args == null) {
			if (other.args != null)
				return false;
		} else if (!args.equals(other.args))
			return false;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		return true;
	}

	@Override
	public String toString() {
		return "PGoTLAFunction [args=" + args + ", body=" + body + ", getLine()=" + getLine() + "]";
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
