package pgo.model.tla;

import pgo.util.SourceLocation;

/**
 * 
 * AST PlusCalNode representing a single identifier. This allows us to attach metadata at
 * the identifier level.
 * 
 */
public class TLAIdentifier extends TLANode {
	
	private String id;
	
	public TLAIdentifier(SourceLocation location, String id) {
		super(location);
		this.id = id;
	}
	
	@Override
	public TLAIdentifier copy() {
		return new TLAIdentifier(getLocation(), id);
	}
	
	@Override
	public <T, E extends Throwable> T accept(TLANodeVisitor<T, E> v) throws E {
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
		TLAIdentifier other = (TLAIdentifier) obj;
		if (id == null) {
			if (other.id != null)
				return false;
		} else if (!id.equals(other.id))
			return false;
		return true;
	}

}
