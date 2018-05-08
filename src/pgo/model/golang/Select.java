package pgo.model.golang;

import java.util.LinkedHashMap;
import java.util.List;

/**
 * A select statement in go
 *
 *
 */
public class Select extends Statement {
	
	LinkedHashMap<Statement, List<Statement>> cases;

	public Select(LinkedHashMap<Statement, List<Statement>> cases) {
		this.cases = cases;
	}

	public LinkedHashMap<Statement, List<Statement>> getCases() {
		return cases;
	}

	@Override
	public <T> T accept(Visitor<T> v) {
		return v.visit(this);
	}

}
