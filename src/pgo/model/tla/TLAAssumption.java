package pgo.model.tla;

import pgo.util.SourceLocation;
import scala.collection.immutable.List;
import scala.collection.immutable.List$;

public class TLAAssumption extends TLAUnit {
	
	private final TLAExpression assumption;

	public TLAAssumption(SourceLocation location, TLAExpression assumption) {
		super(location);
		this.assumption = assumption;
	}

	@Override
	public List<TLADefinition> definitions() {
		return List$.MODULE$.empty();
	}
	
	@Override
	public TLAAssumption copy() {
		return new TLAAssumption(getLocation(), assumption.copy());
	}

	public TLAExpression getAssumption() {
		return assumption;
	}

	@Override
	public <T, E extends Throwable> T accept(TLAUnitVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((assumption == null) ? 0 : assumption.hashCode());
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
		TLAAssumption other = (TLAAssumption) obj;
		if (assumption == null) {
			return other.assumption == null;
		} else return assumption.equals(other.assumption);
	}

}
