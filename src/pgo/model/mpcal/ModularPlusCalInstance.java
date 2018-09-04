package pgo.model.mpcal;

import pgo.TODO;
import pgo.model.tla.TLAExpression;
import pgo.parser.Located;
import pgo.util.SourceLocation;

import java.util.Collections;
import java.util.List;

/**
 * Modular PlusCal instance node
 *
 * instance A(exp, ref global, readOnlyGlobal)
 *     mapping global via MappingMacro;
 *     interleaving goto label;
 */
public class ModularPlusCalInstance extends ModularPlusCalUnit {
	private String target;
	private List<TLAExpression> params;
	private List<ModularPlusCalMapping> mappings;
	private Located<String> interleavingTarget;

	public ModularPlusCalInstance(SourceLocation location, String target, List<TLAExpression> params, List<ModularPlusCalMapping> mappings, Located<String> interleavingTarget) {
		super(location);
		this.target = target;
		this.params = params;
		this.mappings = mappings;
		this.interleavingTarget = interleavingTarget;
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

	public String getTarget() {
		return target;
	}

	public List<ModularPlusCalMapping> getMappings() {
		return Collections.unmodifiableList(mappings);
	}

	public Located<String> getInterleavingTarget() {
		return interleavingTarget;
	}

	public List<TLAExpression> getParams() {
		return Collections.unmodifiableList(params);
	}
}
