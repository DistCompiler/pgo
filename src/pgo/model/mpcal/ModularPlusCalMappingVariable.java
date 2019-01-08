package pgo.model.mpcal;

import pgo.scope.UID;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

public class ModularPlusCalMappingVariable extends SourceLocatable {
	private final SourceLocation location;
	private final UID uid;
	private final String name;
	private final boolean functionCalls;

	public ModularPlusCalMappingVariable(SourceLocation location, String name, boolean functionCalls) {
		this.location = location;
		this.uid = new UID();
		this.uid.addOrigin(this);
		this.name = name;
		this.functionCalls = functionCalls;
	}

	@Override
	public SourceLocation getLocation() {
		return location;
	}

	public UID getUID() {
		return uid;
	}

	public String getName() {
		return name;
	}

	public boolean isFunctionCalls() { return this.functionCalls; }
}
