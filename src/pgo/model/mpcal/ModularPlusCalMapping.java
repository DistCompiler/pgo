package pgo.model.mpcal;

import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

import java.util.Objects;

public class ModularPlusCalMapping extends SourceLocatable {
	private final SourceLocation location;
	private final ModularPlusCalMappingVariable variable;
	private final ModularPlusCalMappingTarget target;

	public ModularPlusCalMapping(SourceLocation location, ModularPlusCalMappingVariable variable,
	                             ModularPlusCalMappingTarget target) {
		this.location = location;
		this.variable = variable;
		this.target = target;
	}

	public ModularPlusCalMapping copy() {
		return new ModularPlusCalMapping(
				getLocation(),
				variable.copy(),
				new ModularPlusCalMappingTarget(target.getLocation(), target.getName()));
	}

	@Override
	public int hashCode() {
		return Objects.hash(variable.hashCode(), target.getName());
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || obj.getClass() != getClass()) {
			return false;
		}
		ModularPlusCalMapping that = (ModularPlusCalMapping) obj;
		return target.getName().equals(that.target.getName()) &&
				variable.equals(that.variable);
	}

	@Override
	public SourceLocation getLocation() {
		return location;
	}

	public ModularPlusCalMappingVariable getVariable() {
		return variable;
	}

	public ModularPlusCalMappingTarget getTarget() {
		return target;
	}
}
