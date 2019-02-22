package pgo.model.type;

import pgo.util.DerivedVisitor;
import pgo.util.Origin;

import java.util.*;
import java.util.stream.Collectors;

public class PGoTypePolymorphicConstraint extends PGoTypeConstraint
		implements Iterator<List<PGoTypeBasicConstraint>>, Iterable<List<PGoTypeBasicConstraint>> {
	private List<List<PGoTypeBasicConstraint>> constraints;
	private int currentIndex;

	public PGoTypePolymorphicConstraint(Origin origin, List<List<PGoTypeBasicConstraint>> constraints) {
		this(Collections.singletonList(origin), constraints);
	}

	PGoTypePolymorphicConstraint(List<Origin> origins, List<List<PGoTypeBasicConstraint>> constraints) {
		origins.forEach(this::addOrigin);
		this.constraints = constraints;
		this.currentIndex = 0;
	}

	@Override
	public <T, E extends Throwable> T accept(DerivedVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean hasNext() {
		return currentIndex < constraints.size();
	}

	@Override
	public List<PGoTypeBasicConstraint> next() {
		int index = currentIndex;
		currentIndex += 1;
		try {
			return constraints.get(index);
		} catch (IndexOutOfBoundsException e) {
			throw new NoSuchElementException();
		}
	}

	@Override
	public PGoTypePolymorphicConstraint copy() {
		List<List<PGoTypeBasicConstraint>> cs = new ArrayList<>();
		for (List<PGoTypeBasicConstraint> equalityConstraints : constraints) {
			cs.add(equalityConstraints.stream().map(PGoTypeBasicConstraint::copy).collect(Collectors.toList()));
		}
		PGoTypePolymorphicConstraint copy = new PGoTypePolymorphicConstraint(getOrigins(), cs);
		copy.currentIndex = currentIndex;
		return copy;
	}

	@Override
	public Iterator<List<PGoTypeBasicConstraint>> iterator() {
		return constraints.listIterator();
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		boolean first = true;
		builder.append("(");
		for (List<PGoTypeBasicConstraint> constraintList : constraints) {
			if (first) {
				first = false;
			} else {
				builder.append(") OR (");
			}
			boolean innerFirst = true;
			for (PGoTypeBasicConstraint constraint : constraintList) {
				if (innerFirst) {
					innerFirst = false;
				} else {
					builder.append(" AND ");
				}
				builder.append(constraint.toString());
			}
		}
		builder.append(")");
		return builder.toString();
	}
}
