package pgo.model.mpcal;

import pgo.TODO;
import pgo.parser.Located;
import pgo.util.SourceLocation;

public class ModularPlusCalVariableDeclaration extends ModularPlusCalNode {
	private Located<String> name;
	private boolean isRef;

	public ModularPlusCalVariableDeclaration(SourceLocation location, Located<String> name, boolean isRef) {
		super(location);
		this.name = name;
		this.isRef = isRef;
	}

	@Override
	public ModularPlusCalNode copy() {
		throw new TODO();
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
