package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents the boolean type.
 */
public class BoolType extends Type {
	public BoolType(List<Origin> origins) {
		super(origins);
	}

	@Override
	public int hashCode() {
		return 2;
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof BoolType;
	}

	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
