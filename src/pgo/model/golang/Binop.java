package pgo.model.golang;

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

}
