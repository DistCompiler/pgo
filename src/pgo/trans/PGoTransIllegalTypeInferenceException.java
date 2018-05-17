package pgo.trans;

public class PGoTransIllegalTypeInferenceException extends PGoTransException {
	public PGoTransIllegalTypeInferenceException(String kind, int line) {
		super("Trying to infer type for " + kind, line);
	}
}
