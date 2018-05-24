package pgo.model.type;

import pgo.errors.IssueContext;
import pgo.util.Origin;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Represents a realized tuple.
 */
public class PGoTypeTuple extends PGoType {
	private List<PGoType> elementTypes;

	public PGoTypeTuple(List<PGoType> elementTypes, Origin... origins) {
		this(elementTypes, Arrays.asList(origins));
	}

	public PGoTypeTuple(List<PGoType> elementTypes, List<Origin> origins) {
		super(origins);
		this.elementTypes = Collections.unmodifiableList(elementTypes);
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
	public boolean contains(PGoTypeVariable v) {
		return elementTypes.stream().anyMatch(t -> t.contains(v));
	}

	@Override
	public boolean containsVariables() {
		return elementTypes.stream().anyMatch(PGoType::containsVariables);
	}

	@Override
	public void collectVariables(Set<PGoTypeVariable> vars) {
		elementTypes.forEach(e -> e.collectVariables(vars));
	}

	@Override
	public PGoType substitute(Map<PGoTypeVariable, PGoType> mapping) {
		elementTypes = elementTypes.stream().map(t -> t.substitute(mapping)).collect(Collectors.toList());
		return this;
	}

	@Override
	public PGoType realize(IssueContext ctx) {
		elementTypes = elementTypes.stream().map(pGoType -> pGoType.realize(ctx)).collect(Collectors.toList());
		return this;
	}

	@Override
	public String toTypeName() {
		return "Tuple[" + elementTypes.stream().map(PGoType::toTypeName).collect(Collectors.joining(", ")) + "]";
	}

	@Override
	public String toGo() {
		return "datatypes.Tuple";
	}
}
