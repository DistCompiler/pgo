package pgo.trans;

import pgo.PGoException;

/**
 * Exception during PlusCal AST to Golang AST translation
 *
 */
public class PGoTransException extends PGoException {

	private static final long serialVersionUID = -1752641749710219477L;
	private static final String prefix = "Translation Error";

	public PGoTransException(String msg) {
		super(prefix, msg);
	}

}
