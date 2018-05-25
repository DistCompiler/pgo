package pgo.model.golang;

import java.util.List;

public class Module extends Node {
	private String name;
	private List<Declaration> declarations;
	private List<String> imports;
	
	public Module(String name, List<String> imports, List<Declaration> declarations) {
		this.name = name;
		this.imports = imports;
		this.declarations = declarations;
	}

	public String getName() {
		return name;
	}

	public List<Declaration> getDeclarations() {
		return declarations;
	}

	public List<String> getImports() {
		return imports;
	}
	
}
