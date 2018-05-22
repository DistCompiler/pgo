package pgo.util;

import pgo.model.type.PGoType;
import pgo.scope.UID;
import pgo.trans.intermediate.OperatorAccessor;

public abstract class DerivedVisitor<T, E extends Throwable> {
	public abstract T visit(UID uid) throws E;
	public abstract T visit(PGoType pGoType) throws E;
	public abstract T visit(OperatorAccessor operatorAccessor) throws E;
}
