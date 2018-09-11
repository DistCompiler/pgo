package pgo.model.mpcal;

import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalStatementVisitor;
import pgo.model.tla.TLAExpression;
import pgo.util.SourceLocation;

import java.util.Objects;

/**
 * Read statement
 *
 * yield exp;
 *
 * where exp may contain $value and $variable
 */
public class ModularPlusCalYield extends PlusCalStatement {
	private final TLAExpression expression;

	public ModularPlusCalYield(SourceLocation location, TLAExpression expression) {
		super(location);
		this.expression = expression;
	}

	@Override
	public ModularPlusCalYield copy() {
		return new ModularPlusCalYield(getLocation(), expression.copy());
	}

	@Override
	public int hashCode() {
		return Objects.hash(expression);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || obj.getClass() != getClass()) {
			return false;
		}
		ModularPlusCalYield that = (ModularPlusCalYield) obj;
		return expression.equals(that.expression);
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public TLAExpression getExpression() {
		return expression;
	}
}
