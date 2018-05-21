package pgo.model.type;

public abstract class PGoTypeException extends RuntimeException {
	public PGoTypeException(String prefix, String msg) {
		super(prefix + ": "+ msg);
	}

	public PGoTypeException(String prefix, String msg, int lineN) {
		super(prefix + ": " + msg + " at line " + Integer.toString(lineN));
	}
}
