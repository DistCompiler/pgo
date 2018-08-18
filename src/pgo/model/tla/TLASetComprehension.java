package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.List;
import java.util.stream.Collectors;

/**
 * 
 * TLA AST PlusCalNode:
 * 
 * { <expr> : a \in S1, << a, b >> \in S2, ... }
 *
 */
public class TLASetComprehension extends TLAExpression {
	
	private TLAExpression body;
	private List<TLAQuantifierBound> bounds;

	public TLASetComprehension(SourceLocation location, TLAExpression body, List<TLAQuantifierBound> bounds) {
		super(location);
		this.body = body;
		this.bounds = bounds;
	}
	
	@Override
	public TLASetComprehension copy() {
		return new TLASetComprehension(getLocation(), body.copy(), bounds.stream().map(TLAQuantifierBound::copy).collect(Collectors.toList()));
	}
	
	public TLAExpression getBody() {
		return body;
	}
	
	public List<TLAQuantifierBound> getBounds(){
		return bounds;
	}

	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((body == null) ? 0 : body.hashCode());
		result = prime * result + ((bounds == null) ? 0 : bounds.hashCode());
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
		TLASetComprehension other = (TLASetComprehension) obj;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		if (bounds == null) {
			return other.bounds == null;
		} else return bounds.equals(other.bounds);
	}

}
