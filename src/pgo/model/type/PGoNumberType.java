package pgo.model.type;

/**
 * Represents the base number type.
 */
public abstract class PGoNumberType extends PGoPrimitiveType {
	/**
	 * @return the specificity (precedence in promotion) of this number type
	 */
	public abstract int getSpecificity();
}
