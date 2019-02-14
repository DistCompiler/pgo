package pgo.model.type;

import pgo.util.Derived;
import pgo.util.DerivedVisitor;
import pgo.util.Origin;

import java.util.List;
import java.util.Map;
import java.util.Set;

public abstract class PGoType extends Derived {
	/**
	 * @param origins track where this type come from
	 */
	public PGoType(List<Origin> origins) {
		origins.forEach(this::addOrigin);
	}

	/**
	 * @param mapping maps type variables to types
	 * @return the type after all substitutions are done
	 */
	public abstract PGoType substitute(Map<PGoTypeVariable, PGoType> mapping);

	/**
	 * @return the string representation of the type
	 */
	public abstract String toTypeName();

	public abstract PGoType copy();

	@Override
	public String toString() {
		return toTypeName();
	}

	@Override
	public <T, E extends Throwable> T accept(DerivedVisitor<T, E> v) throws E{
		return v.visit(this);
	}

	public abstract <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E;
}
