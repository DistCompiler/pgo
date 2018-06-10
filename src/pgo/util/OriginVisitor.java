package pgo.util;

public abstract class OriginVisitor<T, E extends Throwable>{
	public abstract T visit(SourceLocatable sourceLocatable) throws E;
	public abstract T visit(Derived derived) throws E;
}
