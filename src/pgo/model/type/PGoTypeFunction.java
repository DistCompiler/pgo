package pgo.model.type;

import pgo.errors.IssueContext;
import pgo.util.Origin;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Represents the function type.
 */
public class PGoTypeFunction extends PGoType {
	private List<PGoType> paramTypes;
	private PGoType returnType;

	public PGoTypeFunction(List<PGoType> paramTypes, PGoType returnType, List<Origin> origins) {
		super(origins);
		this.paramTypes = paramTypes;
		this.returnType = returnType;
	}

	public List<PGoType> getParamTypes() {
		return Collections.unmodifiableList(paramTypes);
	}

	public PGoType getReturnType() {
		return returnType;
	}

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof PGoTypeFunction)) {
			return false;
		}
		PGoTypeFunction fun = (PGoTypeFunction) obj;
		return paramTypes.equals(fun.paramTypes) && returnType.equals(fun.returnType);
	}

	@Override
	public boolean contains(PGoTypeVariable v) {
		return returnType.contains(v) || paramTypes.stream().anyMatch(t -> t.contains(v));
	}

	@Override
	public boolean containsVariables() {
		return returnType.containsVariables() || paramTypes.stream().anyMatch(PGoType::containsVariables);
	}

	@Override
	public void collectVariables(Set<PGoTypeVariable> vars) {
		paramTypes.forEach(e -> e.collectVariables(vars));
		returnType.collectVariables(vars);
	}

	@Override
	public PGoType substitute(Map<PGoTypeVariable, PGoType> mapping) {
		paramTypes = paramTypes.stream().map(t -> t.substitute(mapping)).collect(Collectors.toList());
		returnType = returnType.substitute(mapping);
		return this;
	}

	@Override
	public PGoType realize(IssueContext ctx) {
		paramTypes = paramTypes.stream().map(pGoType -> pGoType.realize(ctx)).collect(Collectors.toList());
		returnType = returnType.realize(ctx);
		return this;
	}

	@Override
	public String toTypeName() {
		return "Func(" + paramTypes.stream().map(PGoType::toTypeName).collect(Collectors.joining(", ")) +
				") " + returnType.toTypeName();
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
