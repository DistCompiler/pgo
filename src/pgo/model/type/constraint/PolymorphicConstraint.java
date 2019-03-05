package pgo.model.type.constraint;

import pgo.util.DerivedVisitor;
import pgo.util.Origin;

import java.util.*;
import java.util.stream.Collectors;

public class PolymorphicConstraint extends Constraint
		implements Iterator<List<BasicConstraint>>, Iterable<List<BasicConstraint>> {
	private List<List<BasicConstraint>> constraints;
	private int currentIndex;

	public PolymorphicConstraint(Origin origin, List<List<BasicConstraint>> constraints) {
		this(Collections.singletonList(origin), constraints);
	}

	PolymorphicConstraint(List<Origin> origins, List<List<BasicConstraint>> constraints) {
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
	public List<BasicConstraint> next() {
		int index = currentIndex;
		currentIndex += 1;
		try {
			return constraints.get(index);
		} catch (IndexOutOfBoundsException e) {
			throw new NoSuchElementException();
		}
	}

	@Override
	public PolymorphicConstraint copy() {
		List<List<BasicConstraint>> cs = new ArrayList<>();
		for (List<BasicConstraint> equalityConstraints : constraints) {
			cs.add(equalityConstraints.stream().map(BasicConstraint::copy).collect(Collectors.toList()));
		}
		PolymorphicConstraint copy = new PolymorphicConstraint(getOrigins(), cs);
		copy.currentIndex = currentIndex;
		return copy;
	}

	@Override
	public Iterator<List<BasicConstraint>> iterator() {
		return constraints.listIterator();
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		boolean first = true;
		builder.append("(");
		for (List<BasicConstraint> constraintList : constraints) {
			if (first) {
				first = false;
			} else {
				builder.append(") OR (");
			}
			boolean innerFirst = true;
			for (BasicConstraint constraint : constraintList) {
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
