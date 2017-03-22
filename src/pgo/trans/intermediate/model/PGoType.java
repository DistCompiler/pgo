package pgo.trans.intermediate.model;

/**
 * Base class representing all types in pluscal and go
 *
 */
public abstract class PGoType {

	/**
	 * Attempts to infer the type from the given pluscal expressions
	 * 
	 * @return a PGoType of inferred type
	 */
	public static PGoType infer() {
		return null;
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

		@Override
		public String toGoTypeName() {
			return "";
		}

	}

	public boolean equals(PGoType p) {
		return toGoTypeName() == p.toGoTypeName();
	}

}
