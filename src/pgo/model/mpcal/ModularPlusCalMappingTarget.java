package pgo.model.mpcal;

import pgo.scope.UID;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

public class ModularPlusCalMappingTarget extends SourceLocatable {
	private final SourceLocation location;
	private final UID uid;
	private final String name;

	public ModularPlusCalMappingTarget(SourceLocation location, String name) {
		this.location = location;
		this.uid = new UID();
		this.uid.addOrigin(this);
		this.name = name;
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
}
