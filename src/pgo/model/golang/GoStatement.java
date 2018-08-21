package pgo.model.golang;

/**
 * A go code statement
 *
 */
public abstract class GoStatement extends GoNode {
	
	public abstract <T, E extends Throwable> T accept(GoStatementVisitor<T, E> v) throws E;
	
	@Override
	public <T, E extends Throwable> T accept(GoNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
