package pgo.model.pcal;

import pgo.model.tla.TLAExpression;
import pgo.util.SourceLocation;

public class PlusCalAwait extends PlusCalStatement {
	
	private TLAExpression condition;
	
	public PlusCalAwait(SourceLocation location, TLAExpression condition) {
		super(location);
		this.condition = condition;
	}
	
	@Override
	public PlusCalAwait copy() {
		return new PlusCalAwait(getLocation(), condition.copy());
	}
	
	public TLAExpression getCondition() {
		return condition;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalStatementVisitor<T, E> v) throws E {
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
		PlusCalAwait other = (PlusCalAwait) obj;
		if (condition == null) {
			if (other.condition != null)
				return false;
		} else if (!condition.equals(other.condition))
			return false;
		return true;
	}

}
