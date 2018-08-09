package pgo.model.golang;

import java.util.List;
import java.util.Objects;

public class GoSelectCase extends GoNode {
	
	private GoStatement condition;
	private List<GoStatement> block;

	public GoSelectCase(GoStatement condition, List<GoStatement> block) {
		super();
		this.condition = condition;
		this.block = block;
	}

	public GoStatement getCondition() {
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
		GoSelectCase that = (GoSelectCase) o;
		return Objects.equals(condition, that.condition) &&
				Objects.equals(block, that.block);
	}

	@Override
	public int hashCode() {

		return Objects.hash(condition, block);
	}
}
