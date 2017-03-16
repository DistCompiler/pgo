package pgo.trans.intermediate.model;

/**
 * Represents the primitive types from pluscal converted to Go. These are types
 * that correspond to a primitive in go: e.g. int, uints, floats, bool, string
 *
 */
public abstract class PGoPrimitiveType extends PGoType {

	/**
	 * Represents an integer in pluscal, which converts to int in go
	 *
	 */
	public static class PGoInt extends PGoPrimitiveType {

		private static final String goType = "int";
		
		@Override
		public String toGo() {
			return goType;
		}

	}

	/**
	 * Represents a decimal number in pluscal, which converts to float64 in go
	 * 
	 */
	public static class PGoDecimal extends PGoPrimitiveType {

		private static final String goType = "float64";

		@Override
		public String toGo() {
			return goType;
		}

	}

	/**
	 * Represents a natural number in pluscal, which converts to uint64 in go
	 * 
	 */
	public static class PGoNatural extends PGoPrimitiveType {

		private static final String goType = "uint64";

		@Override
		public String toGo() {
			return goType;
		}

	}

	/**
	 * Represents a boolean (a string of "TRUE"/"FALSE") in pluscal, which
	 * converts to bool in go
	 * 
	 */
	public static class PGoBool extends PGoPrimitiveType {

		private static final String goType = "bool";

		@Override
		public String toGo() {
			return goType;
		}

	}

	/**
	 * Represents a String in pluscal, which converts to string in go
	 * 
	 */
	public static class PGoString extends PGoPrimitiveType {

		private static final String goType = "String";

		@Override
		public String toGo() {
			return goType;
		}

	}

}
