package pgo.model.golang;

/**
 * A Go code expression base class
 * 
 */
public abstract class Expression extends Node {

	public abstract <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E;
	
	@Override
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
}