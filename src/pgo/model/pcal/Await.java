package pgo.model.pcal;

import pgo.model.tla.PGoTLAExpression;
import pgo.util.SourceLocation;

public class Await extends Statement {
	
	private PGoTLAExpression condition;
	
	public Await(SourceLocation location, PGoTLAExpression condition) {
		super(location);
		this.condition = condition;
	}
	
	@Override
	public Await copy() {
		return new Await(getLocation(), condition.copy());
	}
	
	public PGoTLAExpression getCondition() {
		return condition;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((condition == null) ? 0 : condition.hashCode());
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
		Await other = (Await) obj;
		if (condition == null) {
			if (other.condition != null)
				return false;
		} else if (!condition.equals(other.condition))
			return false;
		return true;
	}

}
