package pgo.model.golang;

import java.util.Collections;
import java.util.List;
import java.util.Vector;

/**
 * A return keyword in go
 *
 */
public class Return extends Expression {

	// the return value if any
	private Expression value;

	public Return(Expression value) {
		this.value = value;
	}

	public Expression getExpression() {
		return value;
	}

	public void setExpression(Expression e) {
		this.value = e;
	}

	@Override
	public List<String> toGo() {
		if (value == null) {
			return Collections.singletonList("return");
		}
		List<String> valStr = value.toGo();
		Vector<String> ret = new Vector<>();
		ret.add("return " + valStr.get(0));
		valStr = valStr.subList(1, valStr.size());
		addStringsAndIndent(ret, valStr);
		return ret;
	}

}
