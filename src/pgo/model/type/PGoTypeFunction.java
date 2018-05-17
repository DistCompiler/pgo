package pgo.model.type;

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

	public PGoTypeFunction(List<PGoType> paramTypes, PGoType returnType) {
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
		List<PGoType> sub = paramTypes.stream().map(t -> t.substitute(mapping)).collect(Collectors.toList());
		return new PGoTypeFunction(sub, returnType.substitute(mapping));
	}

	@Override
	public PGoType realize() {
		List<PGoType> sub = paramTypes.stream().map(PGoType::realize).collect(Collectors.toList());
		return new PGoTypeFunction(sub, returnType.realize());
	}

	@Override
	public String toTypeName() {
		return "Func(" + paramTypes.stream().map(PGoType::toTypeName).collect(Collectors.joining(", ")) +
				") " + returnType.toTypeName();
	}

	@Override
	public String toGo() {
		return "func(" + paramTypes.stream().map(PGoType::toGo).collect(Collectors.joining(", ")) +
				") " + returnType.toGo();
	}
}
