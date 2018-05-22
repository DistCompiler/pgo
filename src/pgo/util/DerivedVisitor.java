package pgo.util;

import pgo.model.type.PGoType;
import pgo.scope.UID;

public abstract class DerivedVisitor<T, E extends Throwable> {
	public abstract T visit(UID uid) throws E;
	public abstract T visit(PGoType pGoType) throws E;
}
