package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

/*
 * TLA AST Node:
 * 
 * \E a, b, c : <expr>
 * or
 * \EE a, b, c : <expr>
 * 
 */
public class PGoTLAExistential extends PGoTLAExpression {
	
	private List<PGoTLAIdentifier> ids;
	private PGoTLAExpression body;

	public PGoTLAExistential(SourceLocation location, List<PGoTLAIdentifier> ids, PGoTLAExpression body) {
		super(location);
		this.ids = ids;
		this.body = body;
	}
	
	@Override
	public PGoTLAExistential copy() {
		return new PGoTLAExistential(getLocation(), ids.stream().map(PGoTLAIdentifier::copy).collect(Collectors.toList()), body.copy());
	}
	
	public List<PGoTLAIdentifier> getIds(){
		return ids;
	}
	
	public PGoTLAExpression getBody() {
		return body;
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTLAExpressionVisitor<T, E> v) throws E {
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
		PGoTLAExistential other = (PGoTLAExistential) obj;
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
