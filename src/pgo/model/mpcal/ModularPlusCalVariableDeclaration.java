package pgo.model.mpcal;

import pgo.TODO;
import pgo.parser.Located;
import pgo.util.SourceLocation;

public class ModularPlusCalVariableDeclaration extends ModularPlusCalNode {
	private final Located<String> name;
	private final boolean isRef;

	public ModularPlusCalVariableDeclaration(SourceLocation location, Located<String> name, boolean isRef) {
		super(location);
		this.name = name;
		this.isRef = isRef;
	}

	@Override
	public ModularPlusCalVariableDeclaration copy() {
		return new ModularPlusCalVariableDeclaration(getLocation(), name, isRef);
	}

	@Override
	public int hashCode() {
		throw new TODO();
	}

	@Override
	public boolean equals(Object obj) {
		throw new TODO();
	}

	@Override
	public <T, E extends Throwable> T accept(ModularPlusCalNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public Located<String> getName() {
		return name;
	}

	public boolean isRef() {
		return isRef;
	}
}
