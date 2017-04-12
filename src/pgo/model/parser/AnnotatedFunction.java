package pgo.model.parser;

import java.util.Vector;

import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoType;
import pgo.parser.PGoParseException;

/**
 * Represents the information of a function from the pluscal annotations.
 *
 */
public class AnnotatedFunction {

	private Vector<PGoType> args;
	private String name;
	private PGoType rType;

	public AnnotatedFunction(String[] parts) {
		args = new Vector<PGoType>();
		rType = PGoPrimitiveType.inferPrimitiveFromGoTypeName("void");
		int i = 1;
		if (!parts[i].contains("()")) {
			rType = PGoPrimitiveType.inferPrimitiveFromGoTypeName(parts[1]);
			++i;
		} else {
			name = parts[i].substring(0, parts[1].length() - 2);
		}
		for (; i < parts.length; ++i) {
			args.add(PGoPrimitiveType.inferPrimitiveFromGoTypeName(parts[i]));
		}
	}

	public String getName() {
		return name;
	}

	public Vector<PGoType> getArgTypes() {
		return args;
	}

	public PGoType getReturnType() {
		return rType;
	}

	// Fill the PGoFunction with information of this annotation
	public void fillFunction(PGoFunction fun) {
		// TODO Auto-generated method stub

	}

	public static AnnotatedFunction parse(String[] parts, int line) throws PGoParseException {
		boolean error = false;
		if (parts.length < 2) {
			error = true;
		} else if (parts.length == 2 && !parts[1].contains("()")) {
			error = true;
		} else {
			if (!parts[1].contains("()") && !parts[2].contains("()")) {
				error = true;
			}
		}
		if (error) {
			throw new PGoParseException("Annotation of \"func\" requires (<rtype>)? <funcname>() (<argtype>)?+",
					line);
		}
		return new AnnotatedFunction(parts);
	}

}
