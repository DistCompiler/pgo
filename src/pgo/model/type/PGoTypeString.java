package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents the string type.
 */
public class PGoTypeString extends PGoType {
	public PGoTypeString(List<Origin> origins) {
		super(origins);
	}

	@Override
	public int hashCode() {
		return 11;
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeString;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
