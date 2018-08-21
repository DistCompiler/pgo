package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.Objects;

public class TLAFairness extends TLAExpression {

	public enum Type {
		STRONG,
		WEAK,
	}

	private Type type;
	private TLAExpression vars;
	private TLAExpression expression;

	public TLAFairness(SourceLocation location, Type type, TLAExpression vars, TLAExpression expression){
		super(location);
		this.type = type;
		this.vars = vars;
		this.expression = expression;
	}

	public Type getType(){
		return type;
	}

	public TLAExpression getVars(){
		return vars;
	}

	public TLAExpression getExpression(){
		return expression;
	}

	@Override
	public TLAExpression copy() {
		return new TLAFairness(getLocation(), type, vars.copy(), expression.copy());
	}

	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
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
