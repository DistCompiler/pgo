package pgo.model.golang;

public class SwitchCase extends Node {
	private Expression condition;
	private Statement branch;
	
	public SwitchCase(Expression condition, Statement branch) {
		super();
		this.condition = condition;
		this.branch = branch;
	}

	public Expression getCondition() {
		return condition;
	}

	public Statement getBranch() {
		return branch;
	}
	
	@Override
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
