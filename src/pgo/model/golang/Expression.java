package pgo.model.golang;

import java.util.Vector;

/**
 * A Go code expression
 * 
 */
public abstract class Expression extends GoAST {
	public abstract String toGoExpr();

	public Vector<String> toGo() {
		Vector<String> ret = new Vector<String>();
		ret.add(toGoExpr());
		return ret;
	}
}