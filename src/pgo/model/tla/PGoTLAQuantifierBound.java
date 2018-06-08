package pgo.model.tla;

import java.util.List;

public class PGoTLAQuantifierBound {
	
	private List<String> ids;
	private PGoTLAExpression set;

	public PGoTLAQuantifierBound(List<String> ids, PGoTLAExpression set) {
		this.ids = ids;
		this.set = set;
	}
	
	public List<String> getIds(){
		return ids;
	}
	
	public PGoTLAExpression getSet() {
		return set;
	}

	@Override
	public String toString() {
		return "PGoTLAQuantifierBound [ids=" + ids + ", set=" + set + "]";
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
