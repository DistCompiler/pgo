package pgo.trans;

public class PGoTransIllegalConversionException extends PGoTransException {
	public PGoTransIllegalConversionException(String kind, int line) {
		super("Trying to convert " + kind, line);
	}
}
