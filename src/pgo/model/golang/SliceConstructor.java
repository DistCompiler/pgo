package pgo.model.golang;

import java.util.List;

public class SliceConstructor extends Expression {

	private List<Expression> initializers;
	private Type elementType;

	public SliceConstructor(Type elementType, List<Expression> initializers) {
		this.elementType = elementType;
		this.initializers = initializers;
	}
	
	public Type getElementType() {
		return elementType;
	}
	
	public List<Expression> getInitializers(){
		return initializers;
	}

	@Override
	public <T> T accept(Visitor<T> visitor) {
		return visitor.visit(this);
	}

	/*@Override
	public Vector<String> toGo() {
		StringBuilder out = new StringBuilder();
		out.append("[]");
		out.append(elementType.toGo());
		out.append("{");
		boolean first = true;
		for(Expression expr : initializers) {
			if(first) {
				first = false;
			}else {
				out.append(",");
			}
			Vector<String> lines = expr.toGo();
			for(String l : lines) {
				out.append(l);
			}
		}
		out.append("}");
		
		Vector<String> result = new Vector<>();
		result.add(out.toString());
		return result;
	}*/

}
