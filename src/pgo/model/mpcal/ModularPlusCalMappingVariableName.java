package pgo.model.mpcal;

import pgo.util.SourceLocation;

import java.util.Objects;

public class ModularPlusCalMappingVariableName extends ModularPlusCalMappingVariable {
	private final String name;

	public ModularPlusCalMappingVariableName(SourceLocation location, String name, boolean functionCall) {
		super(location, functionCall);
		this.name = name;
	}

	public String getName() {
		return name;
	}

	@Override
	public ModularPlusCalMappingVariableName copy() {
		return new ModularPlusCalMappingVariableName(location, name, functionCall);
	}

	@Override
	public int hashCode() {
		return Objects.hash(name, functionCall);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (!(obj instanceof ModularPlusCalMappingVariableName)) {
			return false;
		}
		ModularPlusCalMappingVariableName other = (ModularPlusCalMappingVariableName) obj;
		return name.equals(other.name) && functionCall == other.functionCall;
	}
}
