package pgo.model.parser;

import pgo.model.intermediate.PGoType;
import pgo.parser.PGoParseException;

/**
 * Represents the annotation that marks a process
 *
 */
public class AnnotatedProcess {

	// the name of the process
	private String name;

	// the type of the id
	private PGoType idType;

	// the line number of the annotation
	private int line;

	protected AnnotatedProcess(String[] parts, int l) throws PGoParseException {
		name = parts[2];
		idType = PGoType.inferFromGoTypeName(parts[1]);
		if (idType.isUndetermined()) {
			throw new PGoParseException("Unknown type name \"" + parts[1] + "\" for process \"" + name + "\"", line);
		}
		line = l;
	}

	public String getName() {
		return name;
	}

	public int getLine() {
		return line;
	}

	public PGoType getIdType() {
		return idType;
	}

	public static AnnotatedProcess parse(String[] parts, int line) throws PGoParseException {
		assert (parts[0].toLowerCase().equals("proc"));

		if (parts.length != 3) {
			throw new PGoParseException(
					"Annotation attribute \"proc\" expects argument <procname> <idtype>. " + parts.length + " provided",
					line);
		}
		return new AnnotatedProcess(parts, line);
	}

}
