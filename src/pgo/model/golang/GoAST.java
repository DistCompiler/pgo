package pgo.model.golang;

import java.util.Vector;

/**
 * The Golang AST base
 *
 */
public abstract class GoAST {

	public abstract Vector<String> toGo();

	public static void addIndented(Vector<String> ret, Vector ast, boolean isString) {
		if (isString) {
			for (String s : (Vector<String>) ast) {
				ret.add("\t" + s);
			}
		} else {
			for (GoAST e : (Vector<GoAST>) ast) {
				for (String s : e.toGo()) {
					ret.add("\t" + s);
				}
			}
		}
	}
	
	// Convenience method for testing
	public boolean equals(Object other) {
		if (!(other instanceof GoAST)) {
			return false;
		}
		GoAST g = (GoAST) other;
		return this.toGo().equals(g.toGo());
	}

	public String toString() {
		String ret = "";
		for (String s : this.toGo()) {
			ret += s + "\n";
		}
		return ret;
	}
}
