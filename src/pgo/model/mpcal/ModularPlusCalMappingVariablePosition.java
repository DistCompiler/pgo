package pgo.model.mpcal;

import pgo.util.SourceLocation;

import java.util.Objects;

public class ModularPlusCalMappingVariablePosition extends ModularPlusCalMappingVariable {
	private final int position;

	public ModularPlusCalMappingVariablePosition(SourceLocation location, int position, boolean functionCall) {
		super(location, functionCall);
		this.position = position;
	}

	public int getPosition() {
		return position;
	}

	@Override
	public ModularPlusCalMappingVariablePosition copy() {
		return new ModularPlusCalMappingVariablePosition(location, position, functionCall);
	}

	@Override
	public int hashCode() {
		return Objects.hash(position, functionCall);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (!(obj instanceof ModularPlusCalMappingVariablePosition)) {
			return false;
		}
		ModularPlusCalMappingVariablePosition other = (ModularPlusCalMappingVariablePosition) obj;
		return position == other.position && functionCall == other.functionCall;
	}

	@Override
	public String toString() {
		return "@" + position + (functionCall ? "[_]" : "");
	}
}
