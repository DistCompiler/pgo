package pgo.model.golang;

import pgo.model.golang.type.GoType;

import java.util.List;
import java.util.Objects;

public class GoSwitchCase extends GoNode {
	private final GoExpression condition;
	private final GoType type;
	private final List<GoStatement> block;
	
	public GoSwitchCase(GoExpression condition, List<GoStatement> block) {
		super();
		this.condition = condition;
		this.block = block;
		this.type = null;
	}

	public GoSwitchCase(GoType type, List<GoStatement> block) {
		super();
		this.type = type;
		this.block = block;
		this.condition = null;
	}

	public GoExpression getCondition() {
		return condition;
	}

	public GoType getType() {
	    return type;
    }

	public List<GoStatement> getBlock() {
		return block;
	}

	public boolean isTypeCase() {
		return type != null;
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
