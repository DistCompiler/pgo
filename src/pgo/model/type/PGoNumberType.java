package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents the base number type.
 */
public abstract class PGoNumberType extends PGoPrimitiveType {
	public PGoNumberType(List<Origin> origins) {
		super(origins);
	}

	/**
	 * @return the specificity (precedence in promotion) of this number type
	 */
	public abstract int getSpecificity();

	/**
	 * Makes a copy with different origins
	 * @param origins the new origins
	 * @return a copy
	 */
	public abstract PGoNumberType copyWithOrigins(List<Origin> origins);
}
