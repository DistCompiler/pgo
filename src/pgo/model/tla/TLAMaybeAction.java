package pgo.model.tla;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST PlusCalNode:
 * 
 * [ <expr> ]_ <expr>
 *
 */
public class TLAMaybeAction extends TLAExpression {

	private final TLAExpression body;
	private final TLAExpression vars;
	
	public TLAMaybeAction(SourceLocation location, TLAExpression body, TLAExpression vars) {
		super(location);
		this.body = body;
		this.vars = vars;
	}
	
	@Override
	public TLAMaybeAction copy() {
		return new TLAMaybeAction(getLocation(), body.copy(), vars.copy());
	}

	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public TLAExpression getBody() {
		return body;
	}
	
	public TLAExpression getVars() {
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
		TLAMaybeAction other = (TLAMaybeAction) obj;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		if (vars == null) {
			return other.vars == null;
		} else return vars.equals(other.vars);
	}
	
}
