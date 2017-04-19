package pgo.model.intermediate;

/**
 * Base class representing all types in pluscal and go
 *
 */
public abstract class PGoType {

	// void type
	public static final PGoType VOID = PGoPrimitiveType.inferPrimitiveFromGoTypeName("void");

	// whether this type is determinable
	protected boolean isUndetermined = false;

	/**
	 * Attempts to infer the type from the given pluscal expressions
	 * 
	 * @return a PGoType of inferred type
	 */
	public static PGoType inferFromGoTypeName(String s) {
		PGoType r = PGoPrimitiveType.inferPrimitiveFromGoTypeName(s);
		if (r.isUndetermined()) {
			r = PGoContainerType.inferContainerFromGoTypeName(s);
		}
		return r;
	}

	/**
	 * 
	 * @return whether the type is undetermined
	 */
	public boolean isUndetermined() {
		return isUndetermined;
	}

	/**
	 * 
	 * @return the go type
	 */
	public abstract String toGoTypeName();

	/**
	 * Represents an indeterminable type
	 *
	 */
	public static class PGoUndetermined extends PGoType {

		public PGoUndetermined() {
			isUndetermined = true;
		}

		@Override
		public String toGoTypeName() {
			return "";
		}

	}

	public boolean equals(PGoType p) {
		return toGoTypeName() == p.toGoTypeName();
	}

}
