package pgo.model.type;

import pgo.errors.IssueContext;
import pgo.util.Origin;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Represents a PlusCal procedure.
 */
public class PGoTypeProcedure extends PGoType {
	private List<PGoType> paramTypes;

	public PGoTypeProcedure(List<PGoType> paramTypes, List<Origin> origins) {
		super(origins);
		this.paramTypes = paramTypes;
	}

	public List<PGoType> getParamTypes() {
		return Collections.unmodifiableList(paramTypes);
	}

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof PGoTypeProcedure)) {
			return false;
		}
		return paramTypes.equals(((PGoTypeProcedure) obj).paramTypes);
	}

	@Override
	public boolean contains(PGoTypeVariable v) {
		return paramTypes.stream().anyMatch(t -> t.contains(v));
	}

	@Override
	public boolean containsVariables() {
		return paramTypes.stream().anyMatch(PGoType::containsVariables);
	}

	@Override
	public void collectVariables(Set<PGoTypeVariable> vars) {
		paramTypes.forEach(t -> t.collectVariables(vars));
	}

	@Override
	public PGoType substitute(Map<PGoTypeVariable, PGoType> mapping) {
		paramTypes = paramTypes.stream().map(t -> t.substitute(mapping)).collect(Collectors.toList());
		return this;
	}

	@Override
	public PGoType realize(IssueContext ctx) {
		paramTypes = paramTypes.stream().map(t -> t.realize(ctx)).collect(Collectors.toList());
		return this;
	}

	@Override
	public String toTypeName() {
		return "PlusCalProcedure(" +
				paramTypes.stream().map(PGoType::toTypeName).collect(Collectors.joining(", ")) +
				")";
	}

	@Override
	public PGoType copy() {
		List<PGoType> params = paramTypes.stream().map(PGoType::copy).collect(Collectors.toList());
		return new PGoTypeProcedure(params, getOrigins());
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
