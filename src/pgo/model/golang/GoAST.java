package pgo.model.golang;

import java.util.List;

/**
 * The Golang AST base
 *
 */
public abstract class GoAST {

	public abstract List<String> toGo();

	/**
	 * Appends ret with a block of code with the correct indentation.
	 * @param ret    the Go code we are adding to
	 * @param ast    the GoAST representation of the indented block
	 */
	public static void addIndentedAST(List<String> ret, List ast) {
		for (GoAST e : (List<GoAST>) ast) {
			addStringsAndIndent(ret, e.toGo());
		}
	}
	
	/**
	 * Appends ret with the strings in toIndent, indented.
	 * @param ret        the strings we are adding to
	 * @param toIndent    the strings we are indenting
	 */
	public static void addStringsAndIndent(List<String> ret, List<String> toIndent) {
		for (String s : toIndent) {
			ret.add("\t" + s);
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
		StringBuilder ret = new StringBuilder();
		for (String s : this.toGo()) {
			ret.append(s).append("\n");
		}
		return ret.toString();
	}
}
