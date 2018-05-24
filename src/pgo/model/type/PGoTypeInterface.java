package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents the interface type.
 */
public class PGoTypeInterface extends PGoPrimitiveType {
	public PGoTypeInterface(Origin... origins) {
		super(origins);
	}

	public PGoTypeInterface(List<Origin> origins) {
		super(origins);
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeInterface;
	}

	@Override
	public String toTypeName() {
		return "Interface";
	}

	@Override
	public String toGo() {
		return "interface{}";
	}
}
