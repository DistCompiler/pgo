package pgo.model.golang;

import java.util.Vector;

/**
 * The Golang AST
 *
 */
public class GoAST {

	// the package name
	private String pkgName;

	private Imports imports;

	public Vector<String> toGo() {
		Vector<String> lines = new Vector<String>();
		lines.add("package " + pkgName);
		lines.addAll(this.imports.toGo());
		return lines;
	}
}
