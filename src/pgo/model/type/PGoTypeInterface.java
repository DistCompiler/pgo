package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

public class PGoTypeInterface extends PGoType {
	/**
	 * @param origins track where this type come from
	 */
	public PGoTypeInterface(List<Origin> origins) {
		super(origins);
	}

	@Override
	public int hashCode() {
		return 5;
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeInterface;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
