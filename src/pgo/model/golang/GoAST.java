package pgo.model.golang;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Vector;

/**
 * The Golang AST
 *
 */
public class GoAST {

	// the package name
	private String pkgName;

	private Imports imports;

	// ordered listing of global variables
	private LinkedHashMap<String, VariableDeclaration> globals;

	// ordered listing of all functions
	private LinkedHashMap<String, Function> funcs;

	// the main function
	private Function main;

	public GoAST() {
	}

	public GoAST(String pkgName) {
		this.pkgName = pkgName;
		this.imports = new Imports();
		this.globals = new LinkedHashMap<String, VariableDeclaration>();
		this.funcs = new LinkedHashMap<String, Function> ();
	}

	public Vector<String> toGo() {
		Vector<String> lines = new Vector<String>();
		lines.add("package " + pkgName);
		lines.add("");
		lines.addAll(this.imports.toGo());
		lines.add("");

		for (VariableDeclaration v : globals.values()) {
			lines.addAll(v.toGo());
		}

		for (Function f : funcs.values()) {
			lines.addAll(f.toGo());
		}

		lines.addAll(main.toGo());

		return lines;
	}

	public static void addIndented(Vector<String> ret, Vector ast) {
		for (GoAST e : (Vector<GoAST>) ast) {
			for (String s : e.toGo()) {
				ret.add("\t" + s);
			}
		}
	}

	public Imports getImports() {
		return imports;
	}

	public List<Function> getFunctions() {
		return new ArrayList<Function>(funcs.values());
	}

	public Function getFunction(String f) {
		return funcs.get(f);
	}

	public void addFunction(Function f) {
		funcs.put(f.getName(), f);
	}

	public List<VariableDeclaration> getGlobals() {
		return new ArrayList<VariableDeclaration>(globals.values());
	}

	public VariableDeclaration getGlobal(String v) {
		return globals.get(v);
	}

	public void addGlobal(VariableDeclaration v) {
		globals.put(v.getName(), v);
	}
}
