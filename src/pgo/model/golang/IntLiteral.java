package pgo.model.golang;

import java.util.Collections;
import java.util.List;

public class IntLiteral extends Expression {

	private int value;

	public IntLiteral(int value) {
		this.value = value;
	}
	
	@Override
	public List<String> toGo() {
		return Collections.singletonList(Integer.toString(value));
	}

}
