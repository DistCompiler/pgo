package pgo.model.type;

import pgo.util.Derived;

/**
 * Represents a type constraint, along with the line from which this constraint
 * originates.
 */
public abstract class PGoTypeConstraint extends Derived {
	public abstract PGoTypeConstraint copy();
}
