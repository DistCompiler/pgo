package pgo.model.tla;

import java.util.List;

public class PGoTLAQuantifierBound {
	
	private List<PGoTLAIdentifierOrTuple> ids;
	private PGoTLAExpression set;

	public PGoTLAQuantifierBound(List<PGoTLAIdentifierOrTuple> ids, PGoTLAExpression set) {
		this.ids = ids;
		this.set = set;
	}
	
	public List<PGoTLAIdentifierOrTuple> getIds(){
		return ids;
	}
	
	public PGoTLAExpression getSet() {
		return set;
	}

	@Override
	public String toString() {
		return "PGoTLAQuantifierBound [ids=" + ids + ", set=" + set + "]";
	}

}
