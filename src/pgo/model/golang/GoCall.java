package pgo.model.golang;

/**
 * A goroutine call
 *
 */
public class GoCall extends Statement {

	private Expression target;

	public GoCall(Expression target) {
		this.target = target;
	}
	
	public Expression getTarget() {
		return target;
	}

	@Override
	public <T> T accept(Visitor<T> v) {
		return v.visit(this);
	}

}
