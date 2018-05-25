package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents an enumerable set.
 */
public class PGoTypeSet extends PGoSimpleContainerType {
	public PGoTypeSet(PGoType elementType, Origin... origins) {
		super(elementType, origins);
	}

	public PGoTypeSet(PGoType elementType, List<Origin> origins) {
		super(elementType, origins);
	}

	@Override
	public boolean equals(Object p) {
		if (!(p instanceof PGoTypeSet)) {
			return false;
		}
		return super.equals(p);
	}

	@Override
	public String toTypeName() {
		return "Set[" + elementType.toTypeName() + "]";
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public String toGo() {
		return "datatypes.Set";
	}

	public boolean isEnumerable() {
		return true;
	}
}
