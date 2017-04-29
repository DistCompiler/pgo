package pgo.model.golang;

import java.util.Vector;

/**
 * The Golang AST base
 *
 */
public abstract class GoAST {

	public abstract Vector<String> toGo();

	public static void addIndented(Vector<String> ret, Vector ast) {
		for (GoAST e : (Vector<GoAST>) ast) {
			for (String s : e.toGo()) {
				ret.add("\t" + s);
			}
		}
	}
}
