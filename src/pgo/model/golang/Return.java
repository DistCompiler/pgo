package pgo.model.golang;

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
	public Vector<String> toGo() {
		if (value == null) {
			return new Vector<String>() {
				{
					add("return");
				}
			};
		}
		Vector<String> valStr = value.toGo();
		Vector<String> ret = new Vector<String>();
		ret.add("return " + valStr.remove(0));
		addIndented(ret, valStr);
		return ret;
	}

}
