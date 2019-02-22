package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

public class PGoTypeAbstractRecord extends PGoType {
	/**
	 * @param origins track where this type come from
	 */
	public PGoTypeAbstractRecord(List<Origin> origins) {
		super(origins);
	}

	@Override
	public int hashCode() {
		return 17;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		return obj instanceof PGoTypeAbstractRecord;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
