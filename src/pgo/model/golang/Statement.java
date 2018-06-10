package pgo.model.golang;

/**
 * A go code statement
 *
 */
public abstract class Statement extends Node {
	
	public abstract <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E;
	
	@Override
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
