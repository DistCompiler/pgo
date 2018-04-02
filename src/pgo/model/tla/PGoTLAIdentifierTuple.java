package pgo.model.tla;

import java.util.ArrayList;
import java.util.List;

/**
 * 
 * AST Node representing:
 * 
 * << a, b, c ... >>
 * 
 */
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
			subs.add(new PGoTLAVariable(id, new ArrayList<>(), line));
		}
		return new PGoTLATuple(line, subs);
	}

	@Override
	public <Result> Result walk(PGoTLAIdentifierOrTupleVisitor<Result> v) {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
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
		PGoTLAIdentifierTuple other = (PGoTLAIdentifierTuple) obj;
		if (ids == null) {
			if (other.ids != null)
				return false;
		} else if (!ids.equals(other.ids))
			return false;
		return true;
	}

}
