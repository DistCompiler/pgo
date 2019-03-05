package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents the string type.
 */
public class StringType extends Type {
	public StringType(List<Origin> origins) {
		super(origins);
	}

	@Override
	public int hashCode() {
		return 11;
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof StringType;
	}

	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
