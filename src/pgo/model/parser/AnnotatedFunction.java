package pgo.model.parser;

import java.util.List;
import java.util.Vector;

import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoVariable;
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeGenerator;
import pgo.model.type.PGoTypeVoid;
import pgo.parser.PGoParseException;
import pgo.trans.PGoAnnotationWrongNameException;
import pgo.trans.PGoTransException;

/**
 * Represents the information of a function from the pluscal annotations.
 *
 */
public class AnnotatedFunction {
	// list of types of the function argument
	private Vector<PGoType> args;

	// the name of function
	private String name;

	// the return type of function
	private PGoType rType;

	// the line number of the annotation
	private int line;

	protected AnnotatedFunction(int line, String[] parts, PGoTypeGenerator generator) throws PGoParseException, PGoTransException {
		args = new Vector<>();
		this.line = line;
		rType = PGoTypeVoid.getInstance();
		int i = 1;
		if (!parts[i].contains("()")) {
			rType = generator.inferFrom(parts[1]);
			++i;
		}

		name = parts[i].substring(0, parts[i].length() - 2);

		for (int j=1; i+j < parts.length; ++j) {
			PGoType aType = generator.inferFrom(parts[i + j]);
			args.add(aType);
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

	public int getLine() {
		return line;
	}

	// Fill the PGoFunction with information of this annotation
	public void applyAnnotationOnFunction(PGoFunction fun, List<AnnotatedReturnVariable> rets) throws PGoTransException {
		if (!fun.getName().equals(name)) {
			throw new PGoAnnotationWrongNameException(name, fun.getName(), line);
		}
		fun.setReturnType(this.rType);
		if (fun.getParams().size() != this.args.size()) {
			throw new PGoTransException(
					"Annotation on line " + this.line + " for function \"" + fun.getName() + "\" has "
							+ this.args.size() + " parameters while actual function has " + fun.getParams().size(),
					fun.getLine());
		}
		for (int i = 0; i < this.args.size(); i++) {
			fun.getParams().get(i).setType(this.args.get(i));
		}

		for (AnnotatedReturnVariable rv : rets) {
			PGoVariable retfv = fun.getVariable(rv.getName());
			if (retfv != null) {
				retfv.setType(this.rType);
				break; // we only support one return value for now. TODO support multiple return types
			}
		}
	}

	public static AnnotatedFunction parse(int line, String[] parts, PGoTypeGenerator generator) throws PGoParseException, PGoTransException {
		if (!parts[0].toLowerCase().equals("func")) {
			throw new IllegalStateException("Trying to apply annotation as a func annotation at line " + line);
		}

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
		return new AnnotatedFunction(line, parts, generator);
	}
}
