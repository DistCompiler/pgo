package pgo.model.tla;

import pgo.util.SourceLocation;

public class PlusCalDefaultInitValue extends PGoTLAExpression {

	public PlusCalDefaultInitValue(SourceLocation location) {
		super(location);
	}

	@Override
	public PGoTLAExpression copy() {
		return new PlusCalDefaultInitValue(getLocation());
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		return 0;
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PlusCalDefaultInitValue;
	}

}
