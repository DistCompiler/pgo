package pgo.model.tla;

import pgo.util.SourceLocation;

public class TLASpecialVariableOld extends TLAExpression {
	public TLASpecialVariableOld(SourceLocation location) {
		super(location);
	}

	@Override
	public int hashCode() {
		return 0;
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof TLASpecialVariableOld;
	}

	@Override
	public TLASpecialVariableOld copy() {
		return new TLASpecialVariableOld(getLocation());
	}

	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
