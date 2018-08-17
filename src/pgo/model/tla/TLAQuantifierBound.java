package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class TLAQuantifierBound extends TLANode {
	
	List<TLAIdentifier> ids;
	TLAExpression set;
	Type type;

	public TLAQuantifierBound(SourceLocation location, Type type, List<TLAIdentifier> ids, TLAExpression set) {
		super(location);
		this.type = type;
		this.ids = ids;
		this.set = set;
	}
	
	public enum Type{
		IDS,
		TUPLE,
	}
	
	@Override
	public TLAQuantifierBound copy() {
		return new TLAQuantifierBound(getLocation(), type, ids.stream().map(TLAIdentifier::copy).collect(Collectors.toList()), set.copy());
	}
	
	public Type getType() {
		return type;
	}
	
	public List<TLAIdentifier> getIds(){
		return ids;
	}
	
	public TLAExpression getSet() {
		return set;
	}
	
	@Override
	public <T, E extends Throwable> T accept(TLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((ids == null) ? 0 : ids.hashCode());
		result = prime * result + ((set == null) ? 0 : set.hashCode());
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
		TLAQuantifierBound other = (TLAQuantifierBound) obj;
		if (ids == null) {
			if (other.ids != null)
				return false;
		} else if (!ids.equals(other.ids))
			return false;
		if (set == null) {
			return other.set == null;
		} else return set.equals(other.set);
	}

}
