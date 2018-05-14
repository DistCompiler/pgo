package pgo.model.tla;

import pgo.util.SourceLocation;

public class PGoTLAModuleDefinition extends PGoTLAUnit {
	
	PGoTLAIdentifier name;
	PGoTLAInstance instance;
	boolean local;

	public PGoTLAModuleDefinition(SourceLocation location, PGoTLAIdentifier name, PGoTLAInstance instance, boolean isLocal) {
		super(location);
		this.name = name;
		this.instance = instance;
		this.local = isLocal;
	}

	public PGoTLAIdentifier getName() {
		return name;
	}

	public PGoTLAInstance getInstance() {
		return instance;
	}
	
	public boolean isLocal() {
		return local;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTLAUnitVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((instance == null) ? 0 : instance.hashCode());
		result = prime * result + (local ? 1231 : 1237);
		result = prime * result + ((name == null) ? 0 : name.hashCode());
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
		PGoTLAModuleDefinition other = (PGoTLAModuleDefinition) obj;
		if (instance == null) {
			if (other.instance != null)
				return false;
		} else if (!instance.equals(other.instance))
			return false;
		if (local != other.local)
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		return true;
	}

}
