package pgo.model.mpcal;

import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.util.SourceLocation;

import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

/**
 * Modular PlusCal instance node
 *
 * process (P \in 1..3) = instance A(exp, ref global, readOnlyGlobal)
 *     mapping global via MappingMacro;
 *     interleaving goto label; // TODO
 */
public class ModularPlusCalInstance extends ModularPlusCalUnit {
	private final PlusCalVariableDeclaration name;
	private final String target;
	private final List<ModularPlusCalVariableDeclaration> params;
	private final List<ModularPlusCalMapping> mappings;
	// TODO
	// private Located<String> interleavingTarget;

	public ModularPlusCalInstance(SourceLocation location, PlusCalVariableDeclaration name, String target,
	                              List<ModularPlusCalVariableDeclaration> params,
	                              List<ModularPlusCalMapping> mappings) {
		super(location);
		this.name = name;
		this.target = target;
		this.params = params;
		this.mappings = mappings;
	}

	@Override
	public ModularPlusCalInstance copy() {
		return new ModularPlusCalInstance(
				getLocation(),
				name.copy(),
				target,
				params.stream().map(ModularPlusCalVariableDeclaration::copy).collect(Collectors.toList()),
				mappings.stream().map(ModularPlusCalMapping::copy).collect(Collectors.toList()));
	}

	@Override
	public int hashCode() {
		return Objects.hash(name, target, params, mappings);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || obj.getClass() != this.getClass()) {
			return false;
		}
		ModularPlusCalInstance that = (ModularPlusCalInstance) obj;
		return target.equals(that.target) &&
				name.equals(that.name) &&
				Objects.equals(params, that.params) &&
				Objects.equals(mappings, that.mappings);
	}

	@Override
	public <T, E extends Throwable> T accept(ModularPlusCalNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public PlusCalVariableDeclaration getName() {
		return name;
	}

	public String getTarget() {
		return target;
	}

	public List<ModularPlusCalMapping> getMappings() {
		return Collections.unmodifiableList(mappings);
	}

	public List<ModularPlusCalVariableDeclaration> getParams() {
		return Collections.unmodifiableList(params);
	}
}
