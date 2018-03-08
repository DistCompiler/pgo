package pgo.model.tla;

import java.util.ArrayList;
import java.util.List;

public class PGoTLAIdentifierTuple extends PGoTLAIdentifierOrTuple {
	
	List<String> ids;
	int line;
	
	public PGoTLAIdentifierTuple(List<String> ids, int line) {
		this.ids = ids;
		this.line = line;
	}
	
	public List<String> getIdentifiers(){
		return ids;
	}
	
	@Override
	public PGoTLAExpression toExpression() {
		List<PGoTLAExpression> subs = new ArrayList<>();
		for(String id : ids) {
			subs.add(new PGoTLAVariable(id, line));
		}
		return new PGoTLATuple(line, subs);
	}

	@Override
	public <Result> Result walk(PGoTLAIdentifierOrTupleVisitor<Result> v) {
		return v.visit(this);
	}

}
