package pgo.model.parser;

import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoVariable;
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeGenerator;
import pgo.parser.PGoParseException;
import pgo.trans.PGoAnnotationWrongNameException;
import pgo.trans.PGoTransException;

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

	protected AnnotatedProcess(int l, String[] parts, PGoTypeGenerator generator) throws PGoParseException, PGoTransException {
		name = parts[2];
		idType = generator.inferFrom(parts[1]);
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

	public static AnnotatedProcess parse(int line, String[] parts, PGoTypeGenerator generator) throws PGoParseException, PGoTransException {
		if (!parts[0].toLowerCase().equals("proc")) {
			throw new PGoParseException("Unknown annotation", line);
		}

		if (parts.length != 3) {
			throw new PGoParseException(
					"Annotation attribute \"proc\" expects argument <procname> <idtype>. " + parts.length + " provided",
					line);
		}
		return new AnnotatedProcess(line, parts, generator);
	}

	/**
	 * Uses the information in the current annotation regarding a process to
	 * fill in information of the corresponding function.
	 * 
	 * This takes the corresponding function and makes sure the self parameter
	 * is of the correct type
	 * 
	 * @param fun
	 * @throws PGoTransException
	 */
	public void applyAnnotationOnFunction(PGoFunction fun) throws PGoTransException {
		if (!fun.getName().equals(name)) {
			throw new PGoAnnotationWrongNameException(name, fun.getName(), line);
		}
		PGoVariable v = fun.getParam(PGoVariable.PROCESS_VAR_ARG);
		if (v == null || fun.getKind() != PGoFunction.FunctionKind.GoRoutine) {
			throw new PGoTransException("Got annotation on line " + line + " for function \"" + name
					+ "\" as a process goroutine function, but actually isn't", fun.getLine());
		}
		v.setType(idType);
	}

}
