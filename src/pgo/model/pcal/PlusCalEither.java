package pgo.model.pcal;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class PlusCalEither extends PlusCalStatement {

	private List<List<PlusCalStatement>> cases;
	
	public PlusCalEither(SourceLocation location, List<List<PlusCalStatement>> cases) {
		super(location);
		this.cases = cases;
	}
	
	@Override
	public PlusCalEither copy() {
		return new PlusCalEither(getLocation(), cases.stream().map(stmts -> {
			return stmts.stream().map(PlusCalStatement::copy).collect(Collectors.toList());
		}).collect(Collectors.toList()));
	}
	
	public List<List<PlusCalStatement>> getCases(){
		return cases;
	}
	
	@Override
	public <T, E extends Throwable> T accept(PlusCalStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((cases == null) ? 0 : cases.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		PlusCalEither other = (PlusCalEither) obj;
		if (cases == null) {
			return other.cases == null;
		} else return cases.equals(other.cases);
	}

}
