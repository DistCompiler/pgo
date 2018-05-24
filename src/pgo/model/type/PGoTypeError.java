package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents the default integer type.
 */
public class PGoTypeError extends PGoPrimitiveType {
	public PGoTypeError(Origin... origins) {
		super(origins);
	}

	public PGoTypeError(List<Origin> origins) {
		super(origins);
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeError;
	}

	@Override
	public String toTypeName() {
		return "Error";
	}

	@Override
	public String toGo() {
		return "error";
	}
}
