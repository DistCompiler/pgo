package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents the floating point number type.
 */
public class PGoTypeDecimal extends PGoNumberType {
	public PGoTypeDecimal(List<Origin> origins) {
		super(origins);
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeDecimal;
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
	public PGoTypeDecimal copyWithOrigins(List<Origin> origins) {
		return new PGoTypeDecimal(origins);
	}
}
