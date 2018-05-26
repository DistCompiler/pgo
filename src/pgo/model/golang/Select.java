package pgo.model.golang;

import java.util.List;

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

}
