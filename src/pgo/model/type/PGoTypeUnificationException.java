package pgo.model.type;

public class PGoTypeUnificationException extends PGoTypeException {
	private static final String PREFIX = "Type unification exception";

	public PGoTypeUnificationException(PGoType a, PGoType b, int line) {
		super(PREFIX, "Unable to unify " + a.toTypeName() + " and " + b.toTypeName(), line);
	}
}
