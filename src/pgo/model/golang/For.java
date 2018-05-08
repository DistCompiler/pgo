package pgo.model.golang;

/**
 * The for loop. Equivalent to PlusCal while
 *
 */
public class For extends Statement {
	// boolean condition
	Statement init;
	Expression cond;
	Statement inc;

	Block body;

	public For(Statement init, Expression cond, Statement inc, Block body) {
		this.init = init;
		this.cond = cond;
		this.inc = inc;
		this.body = body;
	}

	public Statement getInit() {
		return init;
	}
	
	public Expression getCondition() {
		return cond;
	}
	
	public Statement getIncrement() {
		return inc;
	}
	
	public Block getBody() {
		return body;
	}

	@Override
	public <T> T accept(Visitor<T> v) {
		return v.visit(this);
	}
}
