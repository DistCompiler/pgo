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

	public abstract PGoType copy();

	@Override
	public <T, E extends Throwable> T accept(DerivedVisitor<T, E> v) throws E{
		return v.visit(this);
	}

	public abstract <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E;
}
