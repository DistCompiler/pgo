package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.Objects;

public class TLAFairness extends PGoTLAExpression {

	public enum Type {
		STRONG,
		WEAK,
	}

	private Type type;
	private PGoTLAExpression vars;
	private PGoTLAExpression expression;

	public TLAFairness(SourceLocation location, Type type, PGoTLAExpression vars, PGoTLAExpression expression){
		super(location);
		this.type = type;
		this.vars = vars;
		this.expression = expression;
	}

	public Type getType(){
		return type;
	}

	public PGoTLAExpression getVars(){
		return vars;
	}

	public PGoTLAExpression getExpression(){
		return expression;
	}

	@Override
	public PGoTLAExpression copy() {
		return new TLAFairness(getLocation(), type, vars.copy(), expression.copy());
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		TLAFairness that = (TLAFairness) o;
		return type == that.type &&
				Objects.equals(vars, that.vars) &&
				Objects.equals(expression, that.expression);
	}

	@Override
	public int hashCode() {
		return Objects.hash(type, vars, expression);
	}
}
