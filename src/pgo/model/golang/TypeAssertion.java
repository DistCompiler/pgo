package pgo.model.golang;

import java.util.Collections;
import java.util.List;

import pgo.model.type.PGoType;

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
	public List<String> toGo() {
		List<String> ret = expr.toGo();
		assert (ret.size() == 1);
		return Collections.singletonList(ret.get(0) + ".(" + type.toGo() + ")");
	}
}
