package pgo.parser;

public abstract class ActionContext {
	public abstract <T, E extends Throwable> T accept(ActionContextVisitor<T, E> v) throws E;
}
