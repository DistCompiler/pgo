package pgo.model.tla;

import java.util.List;

import pgo.util.SourceLocation;

public class PGoTLAQuantifierBound extends PGoTLANode {
	
	private List<PGoTLAIdentifier> ids;
	private PGoTLAExpression set;

	public PGoTLAQuantifierBound(SourceLocation location, List<PGoTLAIdentifier> ids, PGoTLAExpression set) {
		super(location);
		this.ids = ids;
		this.set = set;
	}
	
	public List<PGoTLAIdentifier> getIds(){
		return ids;
	}
	
	public PGoTLAExpression getSet() {
		return set;
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTLANodeVisitor<T, E> v) throws E {
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
		PGoTLAQuantifierBound other = (PGoTLAQuantifierBound) obj;
		if (ids == null) {
			if (other.ids != null)
				return false;
		} else if (!ids.equals(other.ids))
			return false;
		if (set == null) {
			if (other.set != null)
				return false;
		} else if (!set.equals(other.set))
			return false;
		return true;
	}

}
