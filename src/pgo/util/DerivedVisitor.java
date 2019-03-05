package pgo.util;

import pgo.model.type.constraint.MonomorphicConstraint;
import pgo.model.type.Type;
import pgo.model.type.constraint.PolymorphicConstraint;
import pgo.scope.UID;
import pgo.trans.intermediate.OperatorAccessor;

public abstract class DerivedVisitor<T, E extends Throwable> {
	public abstract T visit(UID uid) throws E;
	public abstract T visit(OperatorAccessor operatorAccessor) throws E;
	public abstract T visit(Type type) throws E;
	public abstract T visit(MonomorphicConstraint pGoTypeMonomorphicConstraint) throws E;
	public abstract T visit(PolymorphicConstraint pGoTypePolymorphicConstraint) throws E;
}
