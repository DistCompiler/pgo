package pgo.model.tla;

import java.util.ArrayList;

/**
 * 
 * AST Node representing a single identifier, in the context of its superclass.
 * 
 */
public class PGoTLAIdentifier extends PGoTLAIdentifierOrTuple {
	
	String id;
	int line;
	
	public PGoTLAIdentifier(String id, int line) {
		this.id = id;
		this.line = line;
	}
	
	public String getId() {
		return id;
	}
	
	@Override
	public PGoTLAExpression toExpression() {
		return new PGoTLAVariable(id, new ArrayList<>(), line);
	}

	@Override
	public <Result> Result walk(PGoTLAIdentifierOrTupleVisitor<Result> v) {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((id == null) ? 0 : id.hashCode());
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
		PGoTLAIdentifier other = (PGoTLAIdentifier) obj;
		if (id == null) {
			if (other.id != null)
				return false;
		} else if (!id.equals(other.id))
			return false;
		return true;
	}

}
