package pgo.model.golang;

import java.util.Vector;

import pgo.model.intermediate.PGoType;

/**
 * Represents a type assertion e.g. x.(int), which casts an interface to the
 * specified type.
 *
 */
public class TypeAssertion extends Expression {
	// the expr we are casting
	private Expression expr;
	
	private PGoType type;
	
	public TypeAssertion(Expression expr, PGoType type) {
		this.expr = expr;
		this.type = type;
	}
	
	@Override
	public Vector<String> toGo() {
		Vector<String> ret = expr.toGo();
		assert(ret.size() == 1);
		ret.set(0, ret.get(0) + ".(" + type.toGo() + ")");
		return ret;
	}
}
