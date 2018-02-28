package pgo.model.golang;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Vector;

/**
 * Represents imports in go. All the importants of the single go program is
 * stored in this data structure. Converting to go, this AST node will
 * properly sort the imports and use the import list syntax of go
 *
 */

public class Imports extends GoAST {

	private Set<String> importPkgs;

	public Imports() {
		importPkgs = new HashSet<>();
	}

	/**
	 * Generates "import pkgname" if only one package Else import( pkg1 \n
	 * pkg2 ... )
	 */
	@Override
	public Vector<String> toGo() {
		Vector<String> ret = new Vector<>();
		if (importPkgs.size() == 0) {
			return ret;
		}
		if (importPkgs.size() == 1) {
			ret.add("import \"" + importPkgs.iterator().next() + "\"");
			return ret;
		}

		List<String> imports = new ArrayList<>(importPkgs);
		Collections.sort(imports);

		ret.add("import (");
		for (String pkg : imports) {
			ret.add("\t\"" + pkg + "\"");
		}
		ret.add(")");
		return ret;
	}
	
	public Vector<String> getImports() {
		return new Vector<>(importPkgs);
	}
	
	public void addImport(String pkg) {
		importPkgs.add(pkg);
	}
	
	public void addAllImports(Set<String> pkgs) {
		importPkgs.addAll(pkgs);
	}

	public void removeImport(String pkg) {
		importPkgs.remove(pkg);
	}
	
	// Return whether pkg is imported by the program.
	public boolean containsPackage(String pkg) {
		return importPkgs.contains(pkg);
	}
}