package pgo.model.golang;

import java.util.Vector;

/**
 * The Golang AST base
 *
 */
public abstract class GoAST {

	public abstract Vector<String> toGo();

	/**
	 * Appends ret with a block of code with the correct indentation.
	 * @param ret	the Go code we are adding to
	 * @param ast	the GoAST representation of the indented block
	 */
	public static void addIndentedAST(Vector<String> ret, Vector ast) {
		for (GoAST e : (Vector<GoAST>) ast) {
			addStringsAndIndent(ret, e.toGo());
		}
	}
	
	/**
	 * Appends ret with the strings in toIndent, indented.
	 * @param ret		the strings we are adding to
	 * @param toIndent	the strings we are indenting
	 */
	public static void addStringsAndIndent(Vector<String> ret, Vector<String> toIndent) {
		for (String s : toIndent) {
			ret.add("\t" + s);
		}
	}

	public String toString() {
		String ret = "";
		for (String s : this.toGo()) {
			ret += s + "\n";
		}
		return ret;
	}
}
