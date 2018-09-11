package pgo.model.tla;

import pgo.util.SourceLocation;

public class TLASpecialVariableVariable extends TLAExpression {
	public TLASpecialVariableVariable(SourceLocation location) {
		super(location);
	}

	@Override
	public int hashCode() {
		return 0;
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof TLASpecialVariableVariable;
	}

	@Override
	public TLASpecialVariableVariable copy() {
		return new TLASpecialVariableVariable(getLocation());
	}

	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
