package pgo.model.type.constraint;

import pgo.model.type.TypeCopyVisitor;
import pgo.model.type.Type;

/**
 * A plain old Java object representing an equality constraint.
 */
public class EqualityConstraint extends BasicConstraint {
	private Type lhs;
	private Type rhs;

	public EqualityConstraint(Type lhs, Type rhs) {
		this.lhs = lhs;
		this.rhs = rhs;
	}

	public Type getLhs() {
		return lhs;
	}

	public Type getRhs() {
		return rhs;
	}

	@Override
	public EqualityConstraint copy() {
		TypeCopyVisitor visitor = new TypeCopyVisitor();
		return new EqualityConstraint(lhs.accept(visitor), rhs.accept(visitor));
	}

	@Override
	public String toString() {
		return lhs.toString() + " = " + rhs.toString();
	}
}
