package pgo.trans.intermediate.model;

/**
 * Represents the various types from pluscal converted to Go.
 *
 */
public class PGoType {

	/**
	 * Represents an integer in pluscal, which converts to int in go
	 *
	 */
	public class PGoInt extends PGoType {

	}

	/**
	 * Represents a decimal number in pluscal, which converts to float64 in go
	 * 
	 */
	public class PGoDecimal extends PGoType {

	}

	/**
	 * Represents a natural number in pluscal, which converts to uint32 in go
	 * 
	 */
	public class PGoNatural extends PGoType {

	}

	/**
	 * Represents a boolean (a string of "TRUE"/"FALSE") in pluscal, which
	 * converts to bool in go
	 * 
	 */
	public class PGoBool extends PGoType {

	}

	/**
	 * Represents a String in pluscal, which converts to string in go
	 * 
	 */
	public class PGoString extends PGoType {

	}

	/**
	 * Represents an Array of elements in pluscal, which converts to array in go
	 * 
	 */
	public class PGoArray extends PGoType {

	}
}
