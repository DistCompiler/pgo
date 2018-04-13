package pgo.model.golang;

import java.util.Vector;

public class IntLiteral extends Expression {

	private int value;

	public IntLiteral(int value) {
		this.value = value;
	}
	
	@Override
	public Vector<String> toGo() {
		Vector<String> result = new Vector<>();
		result.add(Integer.toString(value));
		return result;
	}

}
