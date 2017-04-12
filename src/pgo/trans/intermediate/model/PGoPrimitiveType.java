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
		public String toGoTypeName() {
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
		public String toGoTypeName() {
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
		public String toGoTypeName() {
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
		public String toGoTypeName() {
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
		public String toGoTypeName() {
			return goType;
		}

	}

	/**
	 * Represents a void or no type in pluscal / go
	 * 
	 */
	public static class PGoVoid extends PGoPrimitiveType {
		private static final String goType = "void";

		@Override
		public String toGoTypeName() {
			return goType;
		}
	}

	/**
	 * Attempts to infer the type from a given type name
	 * 
	 * @param string
	 *            the type name, which is one of: int/integer, bool/boolean,
	 *            natural/uint64, decimal/float64, string
	 * @return a PGoType of inferred type
	 */
	public static PGoType inferPrimitiveFromGoTypeName(String string) {
		string = string.toLowerCase();
		switch (string) {
		case "int":
		case "integer":
			return new PGoInt();
		case "bool":
		case "boolean":
			return new PGoBool();
		case "natural":
		case "uint64":
			return new PGoNatural();
		case "decimal":
		case "float64":
			return new PGoDecimal();
		case "string":
			return new PGoString();
		case "void":
			return new PGoVoid();
		}
		return new PGoUndetermined();
	}

}
