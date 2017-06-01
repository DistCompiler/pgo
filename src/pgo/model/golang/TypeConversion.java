package pgo.model.golang;

import java.util.Vector;

import pgo.model.intermediate.PGoType;

/**
 * Represents a type conversion e.g. float64(x).
 */
public class TypeConversion extends FunctionCall {
	public TypeConversion(PGoType type, Expression param) {
		super(type.toGo(), new Vector<Expression>() {
			{
				add(param);
			}
		});
	}
	
	public TypeConversion(String type, Expression param) {
		super(type, new Vector<Expression>() {
			{
				add(param);
			}
		});
	}
}