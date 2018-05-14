package pgo.model.tla;

import java.util.List;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST Node:
 * 
 * ---- ModuleName ----
 * EXTENDS ModuleA, ModuleB
 * ...
 * ====
 *
 */
public class PGoTLAModule extends PGoTLAUnit {
	
	PGoTLAIdentifier name;
	List<PGoTLAIdentifier> exts;
	List<PGoTLAUnit> units;

	public PGoTLAModule(SourceLocation location, PGoTLAIdentifier name, List<PGoTLAIdentifier> exts, List<PGoTLAUnit> units) {
		super(location);
		this.name = name;
		this.exts = exts;
		this.units = units;
	}
	
	public PGoTLAIdentifier getName() {
		return name;
	}
	
	public List<PGoTLAIdentifier> getExtends(){
		return exts;
	}
	
	public List<PGoTLAUnit> getUnits(){
		return units;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTLAUnitVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((exts == null) ? 0 : exts.hashCode());
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((units == null) ? 0 : units.hashCode());
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
		PGoTLAModule other = (PGoTLAModule) obj;
		if (exts == null) {
			if (other.exts != null)
				return false;
		} else if (!exts.equals(other.exts))
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (units == null) {
			if (other.units != null)
				return false;
		} else if (!units.equals(other.units))
			return false;
		return true;
	}
	
}
