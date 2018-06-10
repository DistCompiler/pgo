package pgo.model.golang;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Vector;

public final class Builder {

	private Builder() {}
	
	public static SliceLiteral sliceLiteral(Type elementType, Expression... values) {
		return sliceLiteral(elementType, Arrays.asList(values));
	}
	
	public static SliceLiteral sliceLiteral(Type elementType, List<Expression> values) {
		return new SliceLiteral(elementType, values);
	}
	
	public static StringLiteral stringLiteral(String value) {
		return new StringLiteral(value);
	}
	
	public static MapLiteral mapLiteral(Type keyType, Type valueType, Object[]... pairs) {
		return mapLiteral(keyType, valueType, Arrays.asList(pairs));
	}
	
	public static MapLiteral mapLiteral(Type keyType, Type valueType, List<Object[]> pairs) {
		HashMap<Expression, Expression> map = new HashMap<>();
		for(Object[] pair : pairs) {
			map.put((Expression)pair[0], (Expression)pair[1]);
		}
		return new MapLiteral(keyType, valueType, map);
	}
	
	public static IntLiteral intLiteral(int value) {
		return new IntLiteral(value);
	}
	
	public static Vector<Statement> stmts(Statement... statements) {
		return new Vector<>(Arrays.asList(statements));
	}
	
	public static PtrType ptr(Type type) {
		return new PtrType(type);
	}

}
