package pgo.model.tla;

import pgo.util.SourceLocation;
import scala.collection.immutable.Map$;
import scala.collection.immutable.Map;

/**
 * 
 * AST PlusCalNode representing a single identifier. This allows us to attach metadata at
 * the identifier level.
 * 
 */
public class TLAIdentifier extends TLANode implements TLADefinitionOne {
	
	private final String id;
	
	public TLAIdentifier(SourceLocation location, String id) {
		super(location);
		this.id = id;
	}
	
	@Override
	public TLAIdentifier copy() {
		throw new RuntimeException("bad");
		//return new TLAIdentifier(getLocation(), id);
	}
	
	@Override
	public <T, E extends Throwable> T accept(TLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public String getId() {
		return id;
	}

	@Override
	public int arity() {
		return 0;
	}

	@Override
	public boolean isModuleInstance() {
		return false;
	}

	@Override
	public TLAIdentifier identifier() {
		return this;
	}

	@Override
	public Map<TLAIdentifier, TLADefinitionOne> scope() {
		return Map$.MODULE$.empty();
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
			return other.id == null;
		} else return id.equals(other.id);
	}
}
