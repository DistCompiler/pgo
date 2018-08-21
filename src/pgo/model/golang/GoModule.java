package pgo.model.golang;

import java.util.List;
import java.util.Objects;

public class GoModule extends GoNode {
	private String name;
	private List<GoDeclaration> declarations;
	private List<String> imports;
	private GoExpression pack;
	
	public GoModule(String name, GoExpression pack, List<String> imports, List<GoDeclaration> declarations) {
		this.name = name;
		this.pack = pack;
		this.imports = imports;
		this.declarations = declarations;
	}

	public String getName() {
		return name;
	}
	
	public GoExpression getPackage() {
		return pack;
	}

	public List<GoDeclaration> getDeclarations() {
		return declarations;
	}

	public List<String> getImports() {
		return imports;
	}

	@Override
	public <T, E extends Throwable> T accept(GoNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoModule module = (GoModule) o;
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
