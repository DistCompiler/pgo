package pgo.model.type;

public class PGoTypeRealizationException extends PGoTypeException {
	private static String PREFIX = "Type realization exception";

	public PGoTypeRealizationException(PGoType t) {
		super(PREFIX, "Unable to realize type " + t.toTypeName());
	}

	public PGoTypeRealizationException(PGoType t, int lineN) {
		super(PREFIX, "Unable to realize type " + t.toTypeName(), lineN);
	}
}
