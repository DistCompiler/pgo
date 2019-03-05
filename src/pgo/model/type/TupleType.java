package pgo.model.type;

import pgo.util.Origin;

import java.util.Collections;
import java.util.List;

/**
 * Represents a realized tuple.
 */
public class TupleType extends Type {
	private List<Type> elementTypes;

	public TupleType(List<Type> elementTypes, List<Origin> origins) {
		super(origins);
		this.elementTypes = Collections.unmodifiableList(elementTypes);
	}

	void setElementTypes(List<Type> elementTypes) {
		this.elementTypes = elementTypes;
	}

	public List<Type> getElementTypes() {
		return elementTypes;
	}

	@Override
	public int hashCode() {
		return elementTypes.hashCode() * 17 + 3;
	}

	@Override
	public boolean equals(Object p) {
		if (!(p instanceof TupleType)) {
			return false;
		}
		return elementTypes.equals(((TupleType) p).elementTypes);
	}

	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
