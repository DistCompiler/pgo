package pgo.model.golang;

import java.util.Objects;

public class GoUnary extends GoExpression {

	GoExpression target;
	private final Operation op;

	public enum Operation {
		POS,
		NEG,
		NOT,
		COMPLEMENT,
		DEREF,
		ADDR,
		RECV,
	}

	public GoUnary(Operation op, GoExpression target) {
		this.op = op;
		this.target = target;
	}

	public Operation getOperation() {
		return op;
	}

	public GoExpression getTarget() {
		return target;
	}

	@Override
	public <T, E extends Throwable> T accept(GoExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoUnary unary = (GoUnary) o;
		return Objects.equals(target, unary.target) &&
				op == unary.op;
	}

	@Override
	public int hashCode() {

		return Objects.hash(target, op);
	}
}
