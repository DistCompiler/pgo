package pgo.model.golang;

import java.util.Objects;

public class Binop extends Expression {
	
	private Expression lhs;
	private Expression rhs;
	private Operation op;
	
	public static enum Operation{
		// grouped by precedence
		OR,
		AND,
		
		EQ,
		NEQ,
		LT,
		LEQ,
		GT,
		GEQ,
		
		PLUS,
		MINUS,
		BOR,
		BXOR,
		
		TIMES,
		DIVIDE,
		MOD,
		LSHIFT,
		RSHIFT,
		BAND,
		BCLEAR,
	}
	
	public Binop(Operation op, Expression lhs, Expression rhs) {
		this.op = op;
		this.lhs = lhs;
		this.rhs = rhs;
	}
	
	public Operation getOperation() {
		return op;
	}
	
	public Expression getLHS() {
		return lhs;
	}
	
	public Expression getRHS() {
		return rhs;
	}

	@Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		Binop binop = (Binop) o;
		return Objects.equals(lhs, binop.lhs) &&
				Objects.equals(rhs, binop.rhs) &&
				op == binop.op;
	}

	@Override
	public int hashCode() {

		return Objects.hash(lhs, rhs, op);
	}
}
