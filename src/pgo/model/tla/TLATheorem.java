package pgo.model.tla;

import pgo.util.SourceLocation;
import scala.collection.immutable.List;
import scala.collection.immutable.List$;

public class TLATheorem extends TLAUnit {
	
	private final TLAExpression theorem;

	@Override
	public List<TLADefinition> definitions() {
		return List$.MODULE$.empty();
	}

	public TLATheorem(SourceLocation location, TLAExpression theorem) {
		super(location);
		this.theorem = theorem;
	}
	
	@Override
	public TLATheorem copy() {
		return new TLATheorem(getLocation(), theorem.copy());
	}

	public TLAExpression getTheorem() {
		return theorem;
	}

	@Override
	public <T, E extends Throwable> T accept(TLAUnitVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((theorem == null) ? 0 : theorem.hashCode());
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
		TLATheorem other = (TLATheorem) obj;
		if (theorem == null) {
			return other.theorem == null;
		} else return theorem.equals(other.theorem);
	}

}
