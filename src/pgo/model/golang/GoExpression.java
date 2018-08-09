package pgo.model.golang;

/**
 * A GoRoutineStatement code expression base class
 * 
 */
public abstract class GoExpression extends GoNode {

	public abstract <T, E extends Throwable> T accept(GoExpressionVisitor<T, E> visitor) throws E;
	
	@Override
	public <T, E extends Throwable> T accept(GoNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
}