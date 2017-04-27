package pgo.model.parser;

import java.util.Collection;
import java.util.LinkedHashMap;

import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoVariable;
import pgo.parser.PGoParseException;
import pgo.trans.PGoTransException;
import pgo.util.PcalASTUtil;

/**
 * Represents the annotation that marks a variable as used to return values in
 * PlusCal TODO support multiple return per function like go
 *
 */
public class AnnotatedReturnVariable {

	// the name of the variable
	private String name;

	// the line number of the annotation
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

	/**
	 * Fix the global variable declaration and function variable declarations
	 * given the data in this class regarding which global variable represents a
	 * return value for functions. TODO why
	 * 
	 * This involves removing the return variable from the global variable list,
	 * and creating a local variable for each function that uses it, typing it
	 * according to the function return type.
	 * 
	 * @throws PGoTransException
	 */
	public void applyAnnotation(LinkedHashMap<String, PGoVariable> globals, Collection<PGoFunction> funcs)
			throws PGoTransException {
		globals.remove(name);
		boolean found = false;
		for (PGoFunction f : funcs) {
			if (f.getType() == PGoFunction.FunctionType.Normal) {
				if (f.getVariable(name) == null) {
					if (PcalASTUtil.containsAssignmentToVar(f.getBody(), name)) {
						PGoVariable retVar = PGoVariable.convert(name, f.getReturnType());
						f.addVariable(retVar);
					}
				} else {
					f.getVariable(name).setType(f.getReturnType());
				}
				found = true;
			}
		}
		if (!found) {
			throw new PGoTransException("Expected procedures that uses \"" + name
					+ "\" as a return variable based on annotation, but found none", line);
		}
		// TODO throw warning for no function containing return variable
	}

}
