package pgo.model.pcal;

import pgo.model.tla.TLAExpression;
import pgo.util.SourceLocation;

public class PlusCalAssert extends PlusCalStatement {
	
	private TLAExpression condition;
	
	public PlusCalAssert(SourceLocation location, TLAExpression condition) {
		super(location);
		this.condition = condition;
	}
	
	public TLAExpression getCondition() {
		return condition;
	}
	
	@Override
	public PlusCalAssert copy() {
		return new PlusCalAssert(getLocation(), condition.copy());
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
		PlusCalAssert other = (PlusCalAssert) obj;
		if (condition == null) {
			if (other.condition != null)
				return false;
		} else if (!condition.equals(other.condition))
			return false;
		return true;
	}

}
