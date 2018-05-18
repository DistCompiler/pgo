package pgo.model.tla;

import pgo.util.SourceLocation;

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
	
	public PGoTLAMaybeAction(SourceLocation location, PGoTLAExpression body, PGoTLAExpression vars) {
		super(location);
		this.body = body;
		this.vars = vars;
	}
	
	@Override
	public PGoTLAMaybeAction copy() {
		return new PGoTLAMaybeAction(getLocation(), body.copy(), vars.copy());
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public PGoTLAExpression getBody() {
		return body;
	}
	
	public PGoTLAExpression getVars() {
		return vars;
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
