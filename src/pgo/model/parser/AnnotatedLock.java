package pgo.model.parser;

import pgo.parser.PGoParseException;

/**
 * Describes whether the compiler should add locks to the algorithm.
 * The annotation is of the form "lock [true|false]";
 *
 */
public class AnnotatedLock {
	// whether the compiler should add locks
	private boolean needsLock;
	// the line
	private int line;

	protected AnnotatedLock(boolean lock, int l) {
		needsLock = lock;
		line = l;
	}

	public static AnnotatedLock parse(int line, String[] parts) throws PGoParseException {
		if (parts.length != 2) {
			throw new PGoParseException(
					"Expected the lock annotation to have 2 parts but found " + parts.length + " instead", line);
		}
		if (!parts[0].toLowerCase().equals("lock")) {
			throw new PGoParseException("Unknown annotation", line);
		}
		if (parts[1].toLowerCase().equals("true")) {
			return new AnnotatedLock(true, line);
		}
		if (parts[1].toLowerCase().equals("false")) {
			return new AnnotatedLock(false, line);
		}
		throw new PGoParseException(
				"Expected lock annotation to be \"true\" or \"false\" but found " + parts[1] + " instead", line);
	}

	public boolean needsLock() {
		return needsLock;
	}

	public int getLine() {
		return line;
	}
}
