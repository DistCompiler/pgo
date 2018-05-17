package pgo.model.type;

import java.util.Map;
import java.util.Set;

public abstract class PGoType {
	/**
	 * @param v the type variable to check for
	 * @return whether this contains the type variable v
	 */
	public abstract boolean contains(PGoTypeVariable v);

	/**
	 * @return whether this contains a type variable
	 */
	public abstract boolean containsVariables();

	/**
	 * Collects all variables within this type into `vars`
	 */
	public abstract void collectVariables(Set<PGoTypeVariable> vars);

	/**
	 * @param mapping maps type variables to types
	 * @return the type after all substitutions are done
	 */
	public abstract PGoType substitute(Map<PGoTypeVariable, PGoType> mapping);

	/**
	 * Realizes all unrealized types
	 */
	public abstract PGoType realize();

	/**
	 * @return the string representation of the type
	 */
	public abstract String toTypeName();

	/**
	 * @return the Go type as a string
	 */
	public abstract String toGo();

	@Override
	public String toString() {
		return toTypeName();
	}
}
