package pgo.model.golang;

import java.util.List;
import java.util.Objects;

/**
 * A return keyword in go
 *
 */
public class GoReturn extends GoStatement {

	// the return value if any
	private List<GoExpression> values;

	public GoReturn(List<GoExpression> values) {
		this.values = values;
	}

	public List<GoExpression> getValues() {
		return values;
	}

	@Override
	public <T, E extends Throwable> T accept(GoStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoReturn aReturn = (GoReturn) o;
		return Objects.equals(values, aReturn.values);
	}

	@Override
	public int hashCode() {

		return Objects.hash(values);
	}
}
