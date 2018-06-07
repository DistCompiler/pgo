package pgo.model.golang;

import java.util.List;
import java.util.Objects;

/**
 * A select statement in go
 */
public class Select extends Statement {
	
	List<SelectCase> cases;

	public Select(List<SelectCase> cases) {
		this.cases = cases;
	}

	public List<SelectCase> getCases() {
		return cases;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		Select select = (Select) o;
		return Objects.equals(cases, select.cases);
	}

	@Override
	public int hashCode() {

		return Objects.hash(cases);
	}
}
