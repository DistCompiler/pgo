package pgo.util;

import pgo.scope.UID;

public abstract class DerivedVisitor<T, E extends Throwable> {

	public abstract T visit(UID uid) throws E;

}
