package pgo.model.golang;

import java.util.List;
import java.util.Objects;

public class SwitchCase extends Node {
	private Expression condition;
	private List<Statement> block;
	
	public SwitchCase(Expression condition, List<Statement> block) {
		super();
		this.condition = condition;
		this.block = block;
	}

	public Expression getCondition() {
		return condition;
	}

	public List<Statement> getBlock() {
		return block;
	}
	
	@Override
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		SwitchCase that = (SwitchCase) o;
		return Objects.equals(condition, that.condition) &&
				Objects.equals(block, that.block);
	}

	@Override
	public int hashCode() {

		return Objects.hash(condition, block);
	}
}
