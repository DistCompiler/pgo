package pgo.model.golang;

import java.util.Collections;

import pgo.model.type.PGoType;

/**
 * Represents a type conversion e.g. float64(x).
 */
public class TypeConversion extends FunctionCall {
	public TypeConversion(PGoType type, Expression param) {
		super(type.toGo(), Collections.singletonList(param));
	}
}