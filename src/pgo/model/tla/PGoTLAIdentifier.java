package pgo.model.tla;

import pgo.util.SourceLocation;

/**
 * 
 * AST Node representing a single identifier. This allows us to attach metadata at
 * the identifier level.
 * 
 */
public class PGoTLAIdentifier extends PGoTLANode {
	
	private String id;
	
	public PGoTLAIdentifier(SourceLocation location, String id) {
		super(location);
		this.id = id;
	}
	
	@Override
	public PGoTLAIdentifier copy() {
		return new PGoTLAIdentifier(getLocation(), id);
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public String getId() {
		return id;
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
