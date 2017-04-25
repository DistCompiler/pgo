package pgo.trans;

import pgo.PGoException;

public class PGoUnsupportedException extends PGoException {

	private static final String prefix = "Currently Unsupported";

	public PGoUnsupportedException(String msg) {
		super(prefix, msg);
	}

}
