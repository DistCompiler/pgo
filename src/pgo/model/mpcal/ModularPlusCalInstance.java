package pgo.model.mpcal;

import pgo.model.pcal.PlusCalFairness;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.TLAExpression;
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
	private final PlusCalFairness fairness;
	private final String target;
	private final List<TLAExpression> arguments;
	private final List<ModularPlusCalMapping> mappings;
	// TODO
	// private final Located<String> interleavingTarget;

	public ModularPlusCalInstance(SourceLocation location, PlusCalVariableDeclaration name, PlusCalFairness fairness,
	                              String target, List<TLAExpression> arguments, List<ModularPlusCalMapping> mappings) {
		super(location);
		this.name = name;
		this.fairness = fairness;
		this.target = target;
		this.arguments = arguments;
		this.mappings = mappings;
	}

	@Override
	public ModularPlusCalInstance copy() {
		return new ModularPlusCalInstance(
				getLocation(),
				name.copy(),
				fairness,
				target,
				arguments.stream().map(TLAExpression::copy).collect(Collectors.toList()),
				mappings.stream().map(ModularPlusCalMapping::copy).collect(Collectors.toList()));
	}

	@Override
	public int hashCode() {
		return Objects.hash(name, target, arguments, mappings);
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
				fairness.equals(that.fairness) &&
				Objects.equals(arguments, that.arguments) &&
				Objects.equals(mappings, that.mappings);
	}

	@Override
	public <T, E extends Throwable> T accept(ModularPlusCalNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public PlusCalVariableDeclaration getName() {
		return name;
	}

	public PlusCalFairness getFairness() {
		return this.fairness;
	}

	public String getTarget() {
		return target;
	}

	public List<ModularPlusCalMapping> getMappings() {
		return Collections.unmodifiableList(mappings);
	}

	public List<TLAExpression> getArguments() {
		return Collections.unmodifiableList(arguments);
	}
}
