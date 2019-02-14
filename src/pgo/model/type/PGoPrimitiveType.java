package pgo.model.type;

import pgo.util.Origin;

import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Contains overloaded methods for a primitive type, for convenience.
 */
public abstract class PGoPrimitiveType extends PGoType {
	public PGoPrimitiveType(List<Origin> origins) {
		super(origins);
	}
}
