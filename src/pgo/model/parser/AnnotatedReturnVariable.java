package pgo.model.parser;

import pgo.parser.PGoParseException;

/**
 * Represents the annotation that marks a variable as used to return values in
 * PlusCal TODO support multiple return per function like go
 *
 */
public class AnnotatedReturnVariable {

	// the name of the variable
	private String name;

	// the line number of the annotaiton
	private int line;

	protected AnnotatedReturnVariable(String n, int l) {
		name = n;
		line = l;
	}

	public String getName() {
		return name;
	}

	public int getLine() {
		return line;
	}

	public static AnnotatedReturnVariable parse(String[] parts, int line) throws PGoParseException {
		assert (parts[0].toLowerCase().equals("ret"));

		if (parts.length != 2) {
			throw new PGoParseException("Annotation attribute \"ret\" expects argument <varname>. None provided",
					line);
		}
		return new AnnotatedReturnVariable(parts[1], line);
	}

}
