package pgo.model.golang;

public class Continue extends Statement {

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
