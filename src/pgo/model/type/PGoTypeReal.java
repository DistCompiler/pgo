package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents the floating point number type.
 */
public class PGoTypeReal extends PGoNumberType {
	public PGoTypeReal(List<Origin> origins) {
		super(origins);
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeReal;
	}

	@Override
	public String toTypeName() {
		return "Decimal";
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int getSpecificity() {
		return 3;
	}

	@Override
	public PGoTypeReal copyWithOrigins(List<Origin> origins) {
		return new PGoTypeReal(origins);
	}
}
