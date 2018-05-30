package pgo.model.type;

import pgo.util.DerivedVisitor;
import pgo.util.Origin;

import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

public class PGoTypePolymorphicConstraint extends PGoTypeConstraint implements Iterator<PGoTypeEqualityConstraint>, Iterable<PGoTypeEqualityConstraint> {
	private List<PGoTypeEqualityConstraint> equalityConstraints;
	private int currentIndex = 0;

	public PGoTypePolymorphicConstraint(Origin origin, List<PGoTypeEqualityConstraint> equalityConstraints) {
		addOrigin(origin);
		this.equalityConstraints = equalityConstraints;
	}

	@Override
	public <T, E extends Throwable> T accept(DerivedVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean hasNext() {
		return currentIndex < equalityConstraints.size();
	}

	@Override
	public PGoTypeEqualityConstraint next() {
		int index = currentIndex;
		currentIndex += 1;
		try {
			return equalityConstraints.get(index);
		} catch (IndexOutOfBoundsException e) {
			throw new NoSuchElementException();
		}
	}

	@Override
	public PGoTypePolymorphicConstraint copy() {
		List<Origin> origins = getOrigins();
		PGoTypePolymorphicConstraint copy = new PGoTypePolymorphicConstraint(origins.get(0), equalityConstraints);
		origins.subList(1, origins.size()).forEach(copy::addOrigin);
		copy.currentIndex = currentIndex;
		return copy;
	}

	@Override
	public Iterator<PGoTypeEqualityConstraint> iterator() {
		return equalityConstraints.listIterator();
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		boolean first = true;
		for (PGoTypeEqualityConstraint equalityConstraint : equalityConstraints) {
			if (first) {
				first = false;
			} else {
				builder.append(" OR ");
			}
			builder.append(equalityConstraint.getLhs());
			builder.append(" = ");
			builder.append(equalityConstraint.getRhs());
		}
		return builder.toString();
	}
}
