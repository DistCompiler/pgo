package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents the string type.
 */
public class PGoTypeString extends PGoPrimitiveType {
	public PGoTypeString(Origin... origins) {
		super(origins);
	}

	public PGoTypeString(List<Origin> origins) {
		super(origins);
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeString;
	}

	@Override
	public String toTypeName() {
		return "String";
	}

	@Override
	public String toGo() {
		return "string";
	}
}
