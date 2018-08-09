package pgo.model.golang;

import java.util.List;
import java.util.Objects;

public class GoSwitchCase extends GoNode {
	private GoExpression condition;
	private List<GoStatement> block;
	
	public GoSwitchCase(GoExpression condition, List<GoStatement> block) {
		super();
		this.condition = condition;
		this.block = block;
	}

	public GoExpression getCondition() {
		return condition;
	}

	public List<GoStatement> getBlock() {
		return block;
	}
	
	@Override
	public <T, E extends Throwable> T accept(GoNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoSwitchCase that = (GoSwitchCase) o;
		return Objects.equals(condition, that.condition) &&
				Objects.equals(block, that.block);
	}

	@Override
	public int hashCode() {

		return Objects.hash(condition, block);
	}
}
