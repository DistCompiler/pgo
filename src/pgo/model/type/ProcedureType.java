package pgo.model.type;

import pgo.util.Origin;

import java.util.Collections;
import java.util.List;

/**
 * Represents a PlusCal procedure.
 */
public class ProcedureType extends Type {
	private List<Type> paramTypes;

	public ProcedureType(List<Type> paramTypes, List<Origin> origins) {
		super(origins);
		this.paramTypes = paramTypes;
	}

	void setParamTypes(List<Type> paramTypes) {
		this.paramTypes = paramTypes;
	}

	public List<Type> getParamTypes() {
		return Collections.unmodifiableList(paramTypes);
	}

	@Override
	public int hashCode() {
		return paramTypes.hashCode() * 17 + 2;
	}

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof ProcedureType)) {
			return false;
		}
		return paramTypes.equals(((ProcedureType) obj).paramTypes);
	}

	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
