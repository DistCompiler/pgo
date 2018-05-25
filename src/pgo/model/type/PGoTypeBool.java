package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents the boolean type.
 */
public class PGoTypeBool extends PGoPrimitiveType {
	public PGoTypeBool(Origin... origins) {
		super(origins);
	}

	public PGoTypeBool(List<Origin> origins) {
		super(origins);
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeBool;
	}

	@Override
	public String toTypeName() {
		return "Bool";
	}

	@Override
	public String toGo() {
		return "bool";
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
