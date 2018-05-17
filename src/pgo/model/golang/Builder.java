package pgo.model.golang;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Vector;

import pgo.model.type.PGoType;

public class Builder {

	private Builder() {}
	
	public static SliceConstructor sliceLiteral(PGoType elementType, Expression... values) {
		return sliceLiteral(elementType, Arrays.asList(values));
	}
	
	public static SliceConstructor sliceLiteral(PGoType elementType, List<Expression> values) {
		return new SliceConstructor(elementType, values);
	}
	
	public static StringLiteral stringLiteral(String value) {
		return new StringLiteral(value);
	}
	
	public static MapConstructor mapLiteral(PGoType keyType, PGoType valueType, Object[]... pairs) {
		return mapLiteral(keyType, valueType, Arrays.asList(pairs));
	}
	
	public static MapConstructor mapLiteral(PGoType keyType, PGoType valueType, List<Object[]> pairs) {
		HashMap<Expression, Expression> map = new HashMap<>();
		for(Object[] pair : pairs) {
			map.put((Expression)pair[0], (Expression)pair[1]);
		}
		return new MapConstructor(keyType, valueType, map);
	}
	
	public static StructDefinition structLiteral(PGoType type, Object[]... pairs) {
		return structLiteral(type, Arrays.asList(pairs));
	}
	
	public static StructDefinition structLiteral(PGoType type, List<Object[]> pairs) {
		StructDefinition def = new StructDefinition(type.toGo(), true);
		for(Object[] pair : pairs) {
			def.addField((String)pair[0], (Expression)pair[1]);
		}
		return def;
	}
	
	public static IntLiteral intLiteral(int value) {
		return new IntLiteral(value);
	}
	
	public static Vector<Statement> stmts(Statement... statements) {
		return new Vector<>(Arrays.asList(statements));
	}

}
