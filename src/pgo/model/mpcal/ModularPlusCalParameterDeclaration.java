package pgo.model.mpcal;

import pgo.model.type.PGoType;
import pgo.parser.Located;
import pgo.util.SourceLocation;

import java.util.Objects;

public class ModularPlusCalParameterDeclaration extends ModularPlusCalNode {
	private final Located<String> name;
	private final boolean isRef;
	private final PGoType type;

	public ModularPlusCalParameterDeclaration(SourceLocation location, Located<String> name, boolean isRef,
	                                          PGoType type) {
		super(location);
		this.name = name;
		this.isRef = isRef;
		this.type = type;
	}

	@Override
	public ModularPlusCalNode copy() {
		return new ModularPlusCalParameterDeclaration(getLocation(), name, isRef, type);
	}

	@Override
	public int hashCode() {
		return Objects.hash(name, isRef, type);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (!(obj instanceof ModularPlusCalParameterDeclaration)) {
			return false;
		}
		ModularPlusCalParameterDeclaration other = (ModularPlusCalParameterDeclaration) obj;
		return name.equals(other.name) && isRef == other.isRef && type.equals(other.type);
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

	public PGoType getType() {
		return type;
	}
}
