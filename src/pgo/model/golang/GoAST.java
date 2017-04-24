package pgo.model.golang;

import java.util.Collections;
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

	/**
	 * A Golang comment
	 *
	 */
	public static class Comment extends GoAST {
		private Vector<String> comment;
		// whether this is a block comment (true) with /* and */ or line comment
		// with "//"
		private boolean block;

		public Comment(Vector<String> comment, boolean b) {
			this.comment = new Vector<String>(comment);
			this.block = b;
		}

		public Vector<String> getComment() {
			return new Vector<String>(comment);
		}

		public void addComment(String c) {
			this.comment.add(c);
		}

		public void removeComment(String c) {
			this.comment.remove(c);
		}

		public boolean getIsBlock() {
			return this.block;
		}

		public void setIsBlock(boolean b) {
			this.block = b;
		}

		@Override
		public Vector<String> toGo() {
			Vector<String> ret = new Vector<String>();
			String linePrefix = block? " * " : "// ";
			
			if (block) {
				ret.add("/**");
			}
			for (String c : comment ) {
				ret.add(linePrefix + c);
			}
			if (block) {
				ret.add("**/");
			}
			return ret;
		}
	}

	/**
	 * Represents a function in go
	 *
	 */
	public static class Function extends GoAST {
		// the function name
		private String fname;
	}

	/**
	 * Represents imports in go. All the importants of the single go program is
	 * stored in this data structure. Converting to go, this AST node will
	 * properly sort the imports and use the import list syntax of go
	 *
	 */

	public static class Imports extends GoAST {

		private Vector<String> importPkgs;

		public Imports() {
			importPkgs = new Vector<String>();
		}

		/**
		 * Generates "import pkgname" if only one package Else import( pkg1 \n
		 * pkg2 ... )
		 */
		@Override
		public Vector<String> toGo() {
			Vector<String> ret = new Vector<String>();
			if (importPkgs.size() == 0) {
				return ret;
			}
			if (importPkgs.size() == 1) {
				ret.add("import " + importPkgs.get(0));
				return ret;
			}

			Collections.sort(importPkgs);

			ret.add("import (");
			for (String pkg : importPkgs) {
				ret.add("\t" + pkg);
			}
			ret.add(")");
			return ret;
		}
		
		public Vector<String> getImports() {
			return new Vector<String>(importPkgs);
		}
		
		public void addImport(String pkg) {
			importPkgs.add(pkg);
		}

		public void removeImport(String pkg) {
			importPkgs.remove(pkg);
		}
	}
}
