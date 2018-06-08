package pgo.model.tla;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

/**
 * 
 * TLA AST Node:
 * 
 * [ <expr> ]_ <expr>
 *
 */
public class PGoTLAMaybeAction extends PGoTLAExpression {

	private PGoTLAExpression body;
	private PGoTLAExpression vars;
	
	public PGoTLAMaybeAction(int line, PGoTLAExpression body, PGoTLAExpression vars) {
		super(line);
		this.body = body;
		this.vars = vars;
	}

	@Override
	public String toString() {
		return "PGoTLAMaybeAction [body=" + body + ", vars=" + vars + ", getLine()=" + getLine() + "]";
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
		result = prime * result + ((body == null) ? 0 : body.hashCode());
		result = prime * result + ((vars == null) ? 0 : vars.hashCode());
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
		PGoTLAMaybeAction other = (PGoTLAMaybeAction) obj;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		if (vars == null) {
			if (other.vars != null)
				return false;
		} else if (!vars.equals(other.vars))
			return false;
		return true;
	}

}
