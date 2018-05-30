package pgo.model.type;

import pgo.formatters.DerivedFormattingVisitor;
import pgo.formatters.IndentingWriter;
import pgo.util.DerivedVisitor;
import pgo.util.Origin;

import java.io.IOException;
import java.io.StringWriter;

public class PGoTypeMonomorphicConstraint extends PGoTypeConstraint {
	private PGoTypeEqualityConstraint equalityConstraint;

	public PGoTypeMonomorphicConstraint(Origin origin, PGoType lhs, PGoType rhs) {
		addOrigin(origin);
		equalityConstraint = new PGoTypeEqualityConstraint(lhs, rhs);
	}

	public PGoType getLhs() {
		return equalityConstraint.getLhs();
	}

	public PGoType getRhs() {
		return equalityConstraint.getRhs();
	}

	@Override
	public <T, E extends Throwable> T accept(DerivedVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public PGoTypeMonomorphicConstraint copy() {
		return this;
	}

	@Override
	public String toString() {
		return getLhs().toString() + " = " + getRhs().toString();
	}
}
