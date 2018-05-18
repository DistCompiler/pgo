package pgo.errors;

public abstract class Context {
	
	public abstract <T, E extends Throwable> T accept(ContextVisitor<T, E> ctx) throws E;

}
