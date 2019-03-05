package pgo.model.mpcal;

import pgo.scope.UID;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

public abstract class ModularPlusCalMappingVariable extends SourceLocatable {
	protected final SourceLocation location;
	protected final UID uid;
	protected final boolean functionCall;

	public ModularPlusCalMappingVariable(SourceLocation location, boolean functionCall) {
		this.location = location;
		this.uid = new UID();
		this.uid.addOrigin(this);
		this.functionCall = functionCall;
	}

	@Override
	public SourceLocation getLocation() {
		return location;
	}

	public UID getUID() {
		return uid;
	}

	public boolean isFunctionCall() {
		return functionCall;
	}

	public abstract ModularPlusCalMappingVariable copy();

	@Override
	public abstract int hashCode();

	@Override
	public abstract boolean equals(Object obj);
}
