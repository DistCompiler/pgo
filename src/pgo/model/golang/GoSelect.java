package pgo.model.golang;

import java.util.List;
import java.util.Objects;

/**
 * A select statement in go
 */
public class GoSelect extends GoStatement {
	
	List<GoSelectCase> cases;

	public GoSelect(List<GoSelectCase> cases) {
		this.cases = cases;
	}

	public List<GoSelectCase> getCases() {
		return cases;
	}

	@Override
	public <T, E extends Throwable> T accept(GoStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoSelect select = (GoSelect) o;
		return Objects.equals(cases, select.cases);
	}

	@Override
	public int hashCode() {

		return Objects.hash(cases);
	}
}
