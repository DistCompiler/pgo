package pgo.model.intermediate;

/**
 * Represents the primitive types from pluscal converted to Go. These are types
 * that correspond to a primitive in go: e.g. int, uints, floats, bool, string
 *
 */
public abstract class PGoPrimitiveType extends PGoType {

	public static final PGoPrimitiveType INT = new PGoInt();
	public static final PGoPrimitiveType UINT64 = new PGoNatural();
	public static final PGoPrimitiveType FLOAT64 = new PGoDecimal();
	public static final PGoPrimitiveType STRING = new PGoString();
	public static final PGoPrimitiveType BOOL = new PGoBool();
	public static final PGoPrimitiveType VOID = new PGoVoid();
	public static final PGoPrimitiveType INTERFACE = new PGoInterface();

	/**
	 * Represents an arbitrary number type. In Go if we use a number e.g. in a
	 * function call, it will automatically take on the correct type.
	 * 
	 */
	public static abstract class PGoNumber extends PGoPrimitiveType {

	}

	/**
	 * Represents an integer in pluscal, which converts to int in go
	 *
	 */
	public static class PGoInt extends PGoNumber {

		private static final String goType = "int";

		@Override
		public String toTypeName() {
			return goType;
		}

	}

	/**
	 * Represents a decimal number in pluscal, which converts to float64 in go
	 * 
	 */
	public static class PGoDecimal extends PGoNumber {

		private static final String goType = "float64";

		@Override
		public String toTypeName() {
			return goType;
		}

	}

	/**
	 * Represents a natural number in pluscal, which converts to uint64 in go
	 * 
	 */
	public static class PGoNatural extends PGoNumber {

		private static final String goType = "uint64";

		@Override
		public String toTypeName() {
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
		public String toTypeName() {
			return goType;
		}

	}

	/**
	 * Represents a String in pluscal, which converts to string in go
	 * 
	 */
	public static class PGoString extends PGoPrimitiveType {

		private static final String goType = "string";

		@Override
		public String toTypeName() {
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
		public String toTypeName() {
			return goType;
		}

		@Override
		public String toGo() {
			return ""; // go has no void, it's just empty
		}
	}

	/**
	 * Represents a dynamically typed variable in Go (the go interface{}).
	 *
	 */
	public static class PGoInterface extends PGoPrimitiveType {

		private static final String goType = "interface";

		@Override
		public String toTypeName() {
			return goType;
		}

		@Override
		public String toGo() {
			return goType + "{}";
		}
	}

	/**
	 * Represents a template argument like the K, V in Map<K, V>. Template
	 * arguments are single-letter. These are used for function signatures of
	 * TLA builtin functions.
	 */
	public static class PGoTemplateArgument extends PGoType {

		private String name;

		public PGoTemplateArgument(String name) {
			assert (name.length() == 1);
			this.name = name;
			hasTemplateArgs = true;
		}

		@Override
		public String toTypeName() {
			return name;
		}

	}

	/**
	 * Attempts to infer the type from a given type name
	 * 
	 * @param string
	 *            the type name, which is one of: int/integer, bool/boolean,
	 *            natural/uint64, decimal/float64, string, or a single character
	 *            (template argument)
	 * @return a PGoType of inferred type
	 */
	public static PGoType inferPrimitiveFromGoTypeName(String string) {
		string = string.toLowerCase();
		switch (string) {
		case "int":
		case "integer":
			return INT;
		case "bool":
		case "boolean":
			return BOOL;
		case "natural":
		case "uint64":
			return UINT64;
		case "decimal":
		case "float64":
			return FLOAT64;
		case "string":
			return STRING;
		case "void":
			return VOID;
		case "interface":
		case "interface{}":
			return INTERFACE;
		}
		if (string.length() == 1) {
			return new PGoTemplateArgument(string);
		}
		return UNDETERMINED;
	}

}
