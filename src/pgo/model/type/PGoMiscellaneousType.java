package pgo.model.type;

/**
 * Contains overloaded methods for miscellaneous types, for convenience.
 */
public abstract class PGoMiscellaneousType extends PGoPrimitiveType {
	protected String goType;

	@Override
	public String toTypeName() {
		return goType;
	}

	@Override
	public String toGo() {
		return goType;
	}
}
