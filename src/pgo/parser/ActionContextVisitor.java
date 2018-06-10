package pgo.parser;

public abstract class ActionContextVisitor<T, E extends Throwable> {

	public abstract T visit(WhileParsingBuiltinToken whileParsingBuiltinToken) throws E;
	public abstract T visit(AfterParsingUnit afterParsingUnit) throws E;

}
