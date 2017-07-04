package pgo.model.golang;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Vector;
import java.util.Set;

import pgo.model.intermediate.PGoType;

/**
 * The AST root that contains the whole program
 *
 */
public class GoProgram extends GoAST {

	// the package name
	private String pkgName;

	private Imports imports;

	// ordered listing of global variables
	private LinkedHashMap<String, VariableDeclaration> globals;

	// ordered listing of all functions
	private LinkedHashMap<String, Function> funcs;

	// the main function
	private Function main;
	
	// the set of labels we use in gotos
	private Set<String> labels;

	public GoProgram(String pkgName) {
		this.pkgName = pkgName;
		this.imports = new Imports();
		this.globals = new LinkedHashMap<String, VariableDeclaration>();
		this.funcs = new LinkedHashMap<String, Function>();
		this.main = new Function("main", PGoType.VOID, new Vector<ParameterDeclaration>(),
				new Vector<VariableDeclaration>(), new Vector<Statement>());
		this.labels = new HashSet<>();
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

		lines.add("");

		for (Function f : funcs.values()) {
			lines.addAll(f.toGo());
		}

		lines.add("");

		lines.addAll(main.toGo());

		return lines;
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

	public Function getMain() {
		return main;
	}

	public void setMain(Function f) {
		this.main = f;
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

	public void addUsedLabels(Set<String> labels) {
		this.labels.addAll(labels);
	}
	
	public boolean isLabelUsed(String label) {
		return labels.contains(label);
	}
}
