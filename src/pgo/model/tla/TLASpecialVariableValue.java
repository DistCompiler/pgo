package pgo.model.tla;

import pgo.util.SourceLocation;

public class TLASpecialVariableValue extends TLAExpression {
	public TLASpecialVariableValue(SourceLocation location) {
		super(location);
	}

	@Override
	public int hashCode() {
		return 0;
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof TLASpecialVariableValue;
	}

	@Override
	public TLASpecialVariableValue copy() {
		return new TLASpecialVariableValue(getLocation());
	}

	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
