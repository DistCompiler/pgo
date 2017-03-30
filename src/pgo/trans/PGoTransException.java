package pgo.trans;

/**
 * Exception during PlusCal AST to Golang AST translation
 *
 */
public class PGoTransException extends Exception {

	private static final long serialVersionUID = -1752641749710219477L;

	public PGoTransException(String msg) {
		super(msg);
	}

}
