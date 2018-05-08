package pgo.model.golang;

public class Binop extends Expression {
	
	Expression lhs;
	Expression rhs;
	Operation op;
	
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
	public <T> T accept(Visitor<T> visitor) {
		return visitor.visit(this);
	}

}
