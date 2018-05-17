package pgo.model.type;

import java.util.Map;
import java.util.Set;

/**
 * Represents a type variable.
 */
public class PGoTypeVariable extends PGoType {
	private String name;

	// The constructor must be kept package protected so that
	// PGoTypeGenerator can safely do its job
	PGoTypeVariable(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	@Override
	public boolean contains(PGoTypeVariable v) {
		// since PGoTypeVariable can only be created by
		// PGoTypeGenerator, it is safe to compare references here
		return this == v;
	}

	@Override
	public boolean containsVariables() {
		return true;
	}

	@Override
	public void collectVariables(Set<PGoTypeVariable> vars) {
		vars.add(this);
	}

	@Override
	public PGoType substitute(Map<PGoTypeVariable, PGoType> mapping) {
		PGoType old = this;
		PGoType sub = mapping.getOrDefault(this, this);
		while (!sub.equals(old)) {
			old = sub;
			sub = sub.substitute(mapping);
		}
		return sub;
	}

	@Override
	public PGoType realize() {
		return this;
	}

	@Override
	public String toTypeName() {
		return name;
	}

	@Override
	public String toGo() {
		throw new RuntimeException("Trying to convert type variable to Go");
	}
}
