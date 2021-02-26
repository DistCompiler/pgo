package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.List;
import java.util.stream.Collectors;

/**
 * 
 * TLA AST PlusCalNode:
 * 
 * \A a, b, c : <expr>
 *
 */
public class TLAQuantifiedUniversal extends TLAExpression {

	private final List<TLAQuantifierBound> ids;
	private final TLAExpression body;

	public TLAQuantifiedUniversal(SourceLocation location, List<TLAQuantifierBound> ids, TLAExpression body) {
		super(location);
		this.ids = ids;
		this.body = body;
	}
	
	@Override
	public TLAQuantifiedUniversal copy() {
		return new TLAQuantifiedUniversal(getLocation(), ids.stream().map(TLAQuantifierBound::copy).collect(Collectors.toList()), body.copy());
	}
	
	public List<TLAQuantifierBound> getIds(){
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
		TLAQuantifiedUniversal other = (TLAQuantifiedUniversal) obj;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		if (ids == null) {
			return other.ids == null;
		} else return ids.equals(other.ids);
	}

}
