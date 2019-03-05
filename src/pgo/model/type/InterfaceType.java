package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

public class InterfaceType extends Type {
	/**
	 * @param origins track where this type come from
	 */
	public InterfaceType(List<Origin> origins) {
		super(origins);
	}

	@Override
	public int hashCode() {
		return 5;
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof InterfaceType;
	}

	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
