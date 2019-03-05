package pgo.model.type.constraint;

import pgo.util.Derived;

/**
 * Represents a type constraint, along with the line from which this constraint
 * originates.
 */
public abstract class Constraint extends Derived {
	public abstract Constraint copy();
}
