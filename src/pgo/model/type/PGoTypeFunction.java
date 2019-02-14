package pgo.model.type;

import pgo.util.Origin;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
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
	public boolean containsVariables() {
		return returnType.containsVariables() || paramTypes.stream().anyMatch(PGoType::containsVariables);
	}

	@Override
	public PGoType substitute(Map<PGoTypeVariable, PGoType> mapping) {
		paramTypes = paramTypes.stream().map(t -> t.substitute(mapping)).collect(Collectors.toList());
		returnType = returnType.substitute(mapping);
		return this;
	}

	@Override
	public PGoType copy() {
		List<PGoType> params = paramTypes.stream().map(PGoType::copy).collect(Collectors.toList());
		return new PGoTypeFunction(params, returnType.copy(), getOrigins());
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
