package pgo.model.type;

import pgo.util.Origin;

import java.util.Collections;
import java.util.List;

/**
 * Represents the function type.
 */
public class FunctionType extends Type {
	private List<Type> paramTypes;
	private Type returnType;

	public FunctionType(List<Type> paramTypes, Type returnType, List<Origin> origins) {
		super(origins);
		this.paramTypes = paramTypes;
		this.returnType = returnType;
	}

	void setParamTypes(List<Type> paramTypes) {
		this.paramTypes = paramTypes;
	}

	public List<Type> getParamTypes() {
		return Collections.unmodifiableList(paramTypes);
	}

	void setReturnType(Type returnType) {
		this.returnType = returnType;
	}

	public Type getReturnType() {
		return returnType;
	}

	@Override
	public int hashCode() {
		return paramTypes.hashCode() * 17 + returnType.hashCode() * 19 + 2;
	}

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof FunctionType)) {
			return false;
		}
		FunctionType fun = (FunctionType) obj;
		return paramTypes.equals(fun.paramTypes) && returnType.equals(fun.returnType);
	}

	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
