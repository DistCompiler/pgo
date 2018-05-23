package pgo.model.type;

import java.util.*;

import pgo.errors.IssueContext;

/**
 * Represents an unrealized tuple.
 */
public class PGoTypeUnrealizedTuple extends PGoType {
	private HashMap<Integer, PGoType> elementTypes = new HashMap<>();
	private boolean sizeKnown = false;
	private enum RealType {
		Unknown, Chan, Set, Slice, Tuple
	}
	private RealType realType = RealType.Unknown;

	public PGoTypeUnrealizedTuple() {
		this(new HashMap<>());
	}

	public PGoTypeUnrealizedTuple(Map<Integer, PGoType> elementTypes) {
		this(elementTypes, false);
	}

	public PGoTypeUnrealizedTuple(Map<Integer, PGoType> elementTypes, boolean sizeKnown) {
		this.elementTypes.putAll(elementTypes);
		this.sizeKnown = sizeKnown;
	}

	public Map<Integer, PGoType> getElementTypes() {
		return Collections.unmodifiableMap(elementTypes);
	}

	public boolean isSizeKnown() {
		return sizeKnown;
	}

	private int getProbableSize() {
		return elementTypes.keySet().stream().max(Comparator.naturalOrder()).orElse(-1) + 1;
	}

	public void harmonize(IssueContext ctx, PGoTypeSolver solver, PGoSimpleContainerType other) {
		if (sizeKnown || getProbableSize() > 1 || elementTypes.size() > 1) {
			throw new PGoTypeUnificationException(this, other);
		}
		PGoType elemType = other.getElementType();
		if (elementTypes.size() > 0) {
			elementTypes.forEach((k, v) -> solver.accept(new PGoTypeConstraint(this, elemType, v)));
			solver.unify(ctx);
			if (ctx.hasErrors()) {
				return;
			}
		}
		// from this point onward, type unification was successful
		sizeKnown = true;
		if (other instanceof PGoTypeChan) {
			realType = RealType.Chan;
		} else if (other instanceof PGoTypeSet) {
			realType = RealType.Set;
		} else if (other instanceof PGoTypeSlice) {
			realType = RealType.Slice;
		} else {
			throw new PGoTypeRealizationException(this);
		}
		if (elementTypes.size() > 0) {
			elementTypes.forEach((k, v) -> solver.accept(new PGoTypeConstraint(this, elemType, v)));
		}
		elementTypes.clear();
		elementTypes.put(0, elemType);
	}

	public void harmonize(IssueContext ctx, PGoTypeSolver solver, PGoTypeTuple other) {
		List<PGoType> elemTypes = other.getElementTypes();
		int probableSize = getProbableSize();
		if (probableSize > elemTypes.size() || (sizeKnown && probableSize < elemTypes.size())) {
			throw new PGoTypeUnificationException(this, other);
		}
		elementTypes.forEach((k, v) -> solver.accept(new PGoTypeConstraint(this, elemTypes.get(k), v)));
		solver.unify(ctx);
		if (ctx.hasErrors()) {
			return;
		}
		// from this point onward, type unification was successful
		sizeKnown = true;
		realType = RealType.Tuple;
		for (int i = 0; i < elemTypes.size(); i++) {
			if (elementTypes.containsKey(i)) {
				solver.accept(new PGoTypeConstraint(this, elementTypes.get(i), elemTypes.get(i)));
			} else {
				elementTypes.put(i, elemTypes.get(i));
			}
		}
	}

	public void harmonize(IssueContext ctx, PGoTypeSolver solver, PGoTypeUnrealizedTuple other) {
		if (sizeKnown && other.sizeKnown && getProbableSize() != other.getProbableSize()) {
			throw new PGoTypeUnificationException(this, other);
		}
		if (realType != RealType.Unknown && other.realType != RealType.Unknown && realType != other.realType) {
			throw new PGoTypeUnificationException(this, other);
		}
		boolean isSizeKnown = sizeKnown || other.sizeKnown;
		int probableSize = Integer.max(getProbableSize(), other.getProbableSize());
		for (int i = 0; i < probableSize; i++) {
			if (elementTypes.containsKey(i) && other.elementTypes.containsKey(i)) {
				solver.accept(new PGoTypeConstraint(this, elementTypes.get(i), other.elementTypes.get(i)));
			}
		}
		solver.unify(ctx);
		if (ctx.hasErrors()) {
			return;
		}
		// from this point onward, type unification was successful
		sizeKnown = isSizeKnown;
		other.sizeKnown = isSizeKnown;
		if (realType == RealType.Unknown) {
			realType = other.realType;
		}
		if (other.realType == RealType.Unknown) {
			other.realType = realType;
		}
		HashMap<Integer, PGoType> m = new HashMap<>();
		for (int i = 0; i < probableSize; i++) {
			if (elementTypes.containsKey(i) && other.elementTypes.containsKey(i)) {
				solver.accept(new PGoTypeConstraint(this, elementTypes.get(i), other.elementTypes.get(i)));
			}
			if (elementTypes.containsKey(i)) {
				m.put(i, elementTypes.get(i));
			} else if (other.elementTypes.containsKey(i)) {
				m.put(i, other.elementTypes.get(i));
			}
		}
		elementTypes = m;
		other.elementTypes = m;
	}

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof PGoTypeUnrealizedTuple)) {
			return false;
		}
		PGoTypeUnrealizedTuple other = (PGoTypeUnrealizedTuple) obj;
		return sizeKnown == other.sizeKnown && elementTypes.equals(other.elementTypes);
	}

	@Override
	public boolean contains(PGoTypeVariable v) {
		return elementTypes.values().stream().anyMatch(t -> t.contains(v));
	}

	@Override
	public boolean containsVariables() {
		return !sizeKnown || elementTypes.values().stream().anyMatch(PGoType::containsVariables);
	}

	@Override
	public void collectVariables(Set<PGoTypeVariable> vars) {
		elementTypes.values().forEach(t -> t.collectVariables(vars));
	}

	@Override
	public PGoType substitute(Map<PGoTypeVariable, PGoType> mapping) {
		for (int i : elementTypes.keySet()) {
			elementTypes.put(i, elementTypes.get(i).substitute((mapping)));
		}
		return this;
	}

	@Override
	public PGoType realize() {
		if (!sizeKnown || realType == RealType.Unknown ||
				(getProbableSize() != 1 && realType != RealType.Tuple)) {
			throw new PGoTypeRealizationException(this);
		}
		if (realType == RealType.Tuple) {
			List<PGoType> sub = new ArrayList<>();
			for (int i = 0; i < getProbableSize(); i++) {
				if (!elementTypes.containsKey(i)) {
					throw new PGoTypeRealizationException(this);
				}
				sub.add(elementTypes.get(i).realize());
			}
			return new PGoTypeTuple(sub);
		}
		PGoType elemType = elementTypes.get(0);
		switch (realType) {
			case Chan:
				return new PGoTypeChan(elemType);
			case Set:
				return new PGoTypeSet(elemType);
			case Slice:
				return new PGoTypeSlice(elemType);
			case Tuple:
			case Unknown:
			default:
				throw new RuntimeException("Impossible");
		}
	}

	@Override
	public String toTypeName() {
		StringBuilder s = new StringBuilder();
		s.append("UnrealizedTuple");
		switch (realType) {
			case Chan:
				s.append("<").append("Chan").append(">");
				break;
			case Set:
				s.append("<").append("Set").append(">");
				break;
			case Slice:
				s.append("<").append("Slice").append(">");
				break;
			case Tuple:
				s.append("<").append("Tuple").append(">");
				break;
			case Unknown:
			default:
				// nothing
		}
		s.append("[");
		int probableSize = getProbableSize();
		for (int i = 0; i < probableSize; i++) {
			if (elementTypes.containsKey(i)) {
				s.append(elementTypes.get(i).toTypeName());
			} else {
				s.append("?");
			}
			if (i != probableSize - 1) {
				s.append(", ");
			}
		}
		if (!sizeKnown && probableSize > 0) {
			s.append(", ...?");
		}
		if (!sizeKnown && probableSize == 0) {
			s.append("...?");
		}
		s.append("]");
		return s.toString();
	}

	@Override
	public String toGo() {
		throw new IllegalStateException("Trying to convert an unrealized tuple to Go");
	}
}
