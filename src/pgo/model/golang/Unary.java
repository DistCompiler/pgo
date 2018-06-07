package pgo.model.golang;

import java.util.Objects;

public class Unary extends Expression {

	Expression target;
	private Operation op;

	public enum Operation {
		POS,
		NEG,
		NOT,
		COMPLEMENT,
		DEREF,
		ADDR,
		RECV,
	}

	public Unary(Operation op, Expression target) {
		this.op = op;
		this.target = target;
	}

	public Operation getOperation() {
		return op;
	}

	public Expression getTarget() {
		return target;
	}

	@Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		Unary unary = (Unary) o;
		return Objects.equals(target, unary.target) &&
				op == unary.op;
	}

	@Override
	public int hashCode() {

		return Objects.hash(target, op);
	}
}
