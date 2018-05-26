package pgo.model.golang;

import java.util.List;

public class SelectCase extends Node {
	
	private Statement condition;
	private List<Statement> block;

	public SelectCase(Statement condition, List<Statement> block) {
		super();
		this.condition = condition;
		this.block = block;
	}

	public Statement getCondition() {
		return condition;
	}

	public List<Statement> getBlock() {
		return block;
	}

	@Override
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
