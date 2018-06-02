package pgo.model.type;

import pgo.util.DerivedVisitor;
import pgo.util.Origin;

import java.util.*;
import java.util.stream.Collectors;

public class PGoTypePolymorphicConstraint extends PGoTypeConstraint implements Iterator<List<PGoTypeEqualityConstraint>>, Iterable<List<PGoTypeEqualityConstraint>> {
	private List<List<PGoTypeEqualityConstraint>> constraints;
	private int currentIndex;

	public PGoTypePolymorphicConstraint(Origin origin, List<List<PGoTypeEqualityConstraint>> constraints) {
		this(Collections.singletonList(origin), constraints);
	}

	PGoTypePolymorphicConstraint(List<Origin> origins, List<List<PGoTypeEqualityConstraint>> constraints) {
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
	public List<PGoTypeEqualityConstraint> next() {
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
		List<List<PGoTypeEqualityConstraint>> cs = new ArrayList<>();
		for (List<PGoTypeEqualityConstraint> equalityConstraints : constraints) {
			cs.add(equalityConstraints.stream().map(PGoTypeEqualityConstraint::copy).collect(Collectors.toList()));
		}
		PGoTypePolymorphicConstraint copy = new PGoTypePolymorphicConstraint(getOrigins(), cs);
		copy.currentIndex = currentIndex;
		return copy;
	}

	@Override
	public Iterator<List<PGoTypeEqualityConstraint>> iterator() {
		return constraints.listIterator();
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		boolean first = true;
		builder.append("(");
		for (List<PGoTypeEqualityConstraint> constraintList : constraints) {
			if (first) {
				first = false;
			} else {
				builder.append(") OR (");
			}
			boolean innerFirst = true;
			for (PGoTypeEqualityConstraint constraint : constraintList) {
				if (innerFirst) {
					innerFirst = false;
				} else {
					builder.append(" AND ");
				}
				builder.append(constraint.getLhs());
				builder.append(" = ");
				builder.append(constraint.getRhs());
			}
		}
		builder.append(")");
		return builder.toString();
	}
}
