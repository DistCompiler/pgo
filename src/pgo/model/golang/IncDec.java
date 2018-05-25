package pgo.model.golang;

public class IncDec extends Statement {
	
	private boolean inc;
	private Expression expression;

	public IncDec(boolean inc, Expression expression) {
		this.inc = inc;
		this.expression = expression;
	}

	public boolean isInc() {
		return inc;
	}

	public Expression getExpression() {
		return expression;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
