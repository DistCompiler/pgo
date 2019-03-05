package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents a fallback integer type.
 */
public class IntType extends Type {
	public IntType(List<Origin> origins) {
		super(origins);
	}

	@Override
	public int hashCode() {
		return 3;
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof IntType;
	}

	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
