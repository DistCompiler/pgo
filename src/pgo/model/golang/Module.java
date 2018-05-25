package pgo.model.golang;

import java.util.List;

public class Module extends Node {
	private String name;
	private List<Declaration> declarations;
	private List<String> imports;
	private Expression pack;
	
	public Module(String name, Expression pack, List<String> imports, List<Declaration> declarations) {
		this.name = name;
		this.pack = pack;
		this.imports = imports;
		this.declarations = declarations;
	}

	public String getName() {
		return name;
	}
	
	public Expression getPackage() {
		return pack;
	}

	public List<Declaration> getDeclarations() {
		return declarations;
	}

	public List<String> getImports() {
		return imports;
	}

	@Override
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
}
