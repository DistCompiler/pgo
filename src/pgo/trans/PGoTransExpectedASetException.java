package pgo.trans;

public class PGoTransExpectedASetException extends PGoTransException {
	public PGoTransExpectedASetException(int line) {
		super("Expected a set", line);
	}
}
