package pgo.model.type;

import pgo.util.Origin;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Represents a realized tuple.
 */
public class PGoTypeTuple extends PGoType {
	private List<PGoType> elementTypes;

	public PGoTypeTuple(List<PGoType> elementTypes, List<Origin> origins) {
		super(origins);
		this.elementTypes = Collections.unmodifiableList(elementTypes);
	}

	void setElementTypes(List<PGoType> elementTypes) {
		this.elementTypes = elementTypes;
	}

	public List<PGoType> getElementTypes() {
		return elementTypes;
	}

	@Override
	public boolean equals(Object p) {
		if (!(p instanceof PGoTypeTuple)) {
			return false;
		}
		return elementTypes.equals(((PGoTypeTuple) p).elementTypes);
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public PGoType copy() {
		return new PGoTypeTuple(elementTypes.stream().map(PGoType::copy).collect(Collectors.toList()), getOrigins());
	}

}
