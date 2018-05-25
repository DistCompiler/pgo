package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents a fallback integer type.
 */
public class PGoTypeInt extends PGoNumberType {
	public PGoTypeInt(Origin... origins) {
		super(origins);
	}

	public PGoTypeInt(List<Origin> origins) {
		super(origins);
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeInt;
	}

	@Override
	public String toTypeName() {
		return "Int";
	}

	@Override
	public String toGo() {
		return "int";
	}

	@Override
	public int getSpecificity() {
		return 2;
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public PGoTypeInt copyWithOrigins(List<Origin> origins) {
		return new PGoTypeInt(origins);
	}
}
