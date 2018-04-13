package pgo.model.golang;

import java.util.Map;
import java.util.Vector;

import pgo.model.intermediate.PGoType;

public class MapConstructor extends Expression {
	
	private Map<Expression, Expression> pairs;
	private PGoType keyType;
	private PGoType valueType;

	public MapConstructor(PGoType keyType, PGoType valueType, Map<Expression, Expression> pairs) {
		this.keyType = keyType;
		this.valueType = valueType;
		this.pairs = pairs;
	}

	@Override
	public Vector<String> toGo() {
		StringBuilder out = new StringBuilder();
		out.append("map[");
		out.append(keyType.toGo());
		out.append("]");
		out.append(valueType.toGo());
		out.append("{");
		boolean first = true;
		for(Map.Entry<Expression, Expression> pair : pairs.entrySet()) {
			if(first) {
				first = false;
			}else {
				out.append(",");
			}
			
			Vector<String> tmp = pair.getKey().toGo();
			for(String s : tmp) {
				out.append(s);
			}
			
			out.append(":");
			
			tmp = pair.getValue().toGo();
			for(String s : tmp) {
				out.append(s);
			}
		}
		out.append("}");
		
		Vector<String> result = new Vector<>();
		result.add(out.toString());
		return result;
	}

}
