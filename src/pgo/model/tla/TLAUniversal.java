package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

/*
 * TLA AST PlusCalNode:
 * 
 * \A a, b, c : <expr>
 * or
 * \AA a, b, c : <expr>
 * 
 */
public class TLAUniversal extends TLAExpression {
	
	private List<TLAIdentifier> ids;
	private TLAExpression body;

	public TLAUniversal(SourceLocation location, List<TLAIdentifier> ids, TLAExpression body) {
		super(location);
		this.ids = ids;
		this.body = body;
	}
	
	@Override
	public TLAUniversal copy() {
		return new TLAUniversal(getLocation(), ids.stream().map(TLAIdentifier::copy).collect(Collectors.toList()), body.copy());
	}
	
	public List<TLAIdentifier> getIds(){
		return ids;
	}
	
	public TLAExpression getBody() {
		return body;
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
		result = prime * result + ((ids == null) ? 0 : ids.hashCode());
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
		TLAUniversal other = (TLAUniversal) obj;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		if (ids == null) {
			if (other.ids != null)
				return false;
		} else if (!ids.equals(other.ids))
			return false;
		return true;
	}

}
