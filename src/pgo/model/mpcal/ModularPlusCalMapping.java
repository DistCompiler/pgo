package pgo.model.mpcal;

import pgo.parser.Located;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

import java.util.Objects;

public class ModularPlusCalMapping extends SourceLocatable {
	private SourceLocation location;
	private Located<String> name;
	private String target;

	public ModularPlusCalMapping(SourceLocation location, Located<String> name, String target) {
		this.location = location;
		this.name = name;
		this.target = target;
	}

	public ModularPlusCalMapping copy() {
		return new ModularPlusCalMapping(getLocation(), name, target);
	}

	@Override
	public int hashCode() {
		return Objects.hash(name, target);
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
		return target.equals(that.target) &&
				name.getValue().equals(that.name.getValue());
	}

	@Override
	public SourceLocation getLocation() {
		return location;
	}

	public Located<String> getName() {
		return name;
	}

	public String getTarget() {
		return target;
	}
}
