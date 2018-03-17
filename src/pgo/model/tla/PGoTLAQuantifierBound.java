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

}
