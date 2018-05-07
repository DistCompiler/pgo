package pgo.trans;

public class PGoTransExpectedSingleExpressionException extends PGoTransException {
	public PGoTransExpectedSingleExpressionException(int line) {
		super("Expected single expression", line);
	}
}
