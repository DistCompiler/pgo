package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents the default integer type.
 */
public class PGoTypeNatural extends PGoNumberType {
	public PGoTypeNatural(Origin... origins) {
		super(origins);
	}

	public PGoTypeNatural(List<Origin> origins) {
		super(origins);
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeNatural;
	}

	@Override
	public String toTypeName() {
		return "Natural";
	}

	@Override
	public String toGo() {
		return "uint64";
	}

	@Override
	public int getSpecificity() {
		return 1;
	}

	@Override
	public PGoTypeNatural copyWithOrigins(List<Origin> origins) {
		return new PGoTypeNatural(origins);
	}
}
