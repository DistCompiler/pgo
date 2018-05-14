package pgo.model.golang;

import java.util.List;
import java.util.Vector;

/**
 * Represents a parenthesized expression.
 *
 */
public class Group extends Expression {
	private Expression inside;
	
	public Group(Expression inside) {
		this.inside = inside;
	}
	
	@Override
	public List<String> toGo() {
		List<String> ret = new Vector<>(inside.toGo());
		ret.set(0, "(" + ret.get(0));
		ret.set(ret.size()-1, ret.get(ret.size()-1) + ")");
		return ret;
	}

}
