package pgo.model.tla;

import java.util.List;

public class PGoTLAIdentifierTuple extends PGoTLAIdentifierOrTuple {
	
	List<String> ids;
	
	public PGoTLAIdentifierTuple(List<String> ids) {
		this.ids = ids;
	}
	
	public List<String> getIdentifiers(){
		return ids;
	}

	@Override
	public <Result> Result walk(PGoTLAIdentifierOrTupleVisitor<Result> v) {
		return v.visit(this);
	}

}
