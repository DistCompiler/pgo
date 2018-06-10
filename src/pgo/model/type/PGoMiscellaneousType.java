package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Contains overloaded methods for miscellaneous types, for convenience.
 */
public abstract class PGoMiscellaneousType extends PGoPrimitiveType {
	protected String goType;

	public PGoMiscellaneousType(List<Origin> origins) {
		super(origins);
	}

	@Override
	public String toTypeName() {
		return goType;
	}

}
