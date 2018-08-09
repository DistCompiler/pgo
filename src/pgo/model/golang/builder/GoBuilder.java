package pgo.model.golang.builder;

import pgo.model.golang.*;
import pgo.model.golang.type.GoType;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Vector;

public final class GoBuilder {

	private GoBuilder() {}
	
	public static GoSliceLiteral sliceLiteral(GoType elementType, GoExpression... values) {
		return sliceLiteral(elementType, Arrays.asList(values));
	}
	
	public static GoSliceLiteral sliceLiteral(GoType elementType, List<GoExpression> values) {
		return new GoSliceLiteral(elementType, values);
	}
	
	public static GoStringLiteral stringLiteral(String value) {
		return new GoStringLiteral(value);
	}
	
	public static GoMapLiteral mapLiteral(GoType keyType, GoType valueType, Object[]... pairs) {
		return mapLiteral(keyType, valueType, Arrays.asList(pairs));
	}
	
	public static GoMapLiteral mapLiteral(GoType keyType, GoType valueType, List<Object[]> pairs) {
		HashMap<GoExpression, GoExpression> map = new HashMap<>();
		for(Object[] pair : pairs) {
			map.put((GoExpression)pair[0], (GoExpression)pair[1]);
		}
		return new GoMapLiteral(keyType, valueType, map);
	}
	
	public static GoIntLiteral intLiteral(int value) {
		return new GoIntLiteral(value);
	}
	
	public static Vector<GoStatement> stmts(GoStatement... statements) {
		return new Vector<>(Arrays.asList(statements));
	}
	
	public static GoPtrType ptr(GoType type) {
		return new GoPtrType(type);
	}

}
