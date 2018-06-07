package pgo.model.golang;

import java.util.List;
import java.util.Objects;

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

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		Module module = (Module) o;
		return Objects.equals(name, module.name) &&
				Objects.equals(declarations, module.declarations) &&
				Objects.equals(imports, module.imports) &&
				Objects.equals(pack, module.pack);
	}

	@Override
	public int hashCode() {

		return Objects.hash(name, declarations, imports, pack);
	}
}
