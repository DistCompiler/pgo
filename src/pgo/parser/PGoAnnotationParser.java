package pgo.parser;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.Vector;

import pgo.trans.intermediate.model.AnnotatedFunction;
import pgo.trans.intermediate.model.AnnotatedVariable;
import pgo.trans.intermediate.model.PGoAnnotation;

/**
 * Parses the annotations of the pluscal algorithm for pgo
 *
 */
public class PGoAnnotationParser {

	private LinkedHashMap<String, AnnotatedVariable> vars;
	private LinkedHashMap<String, AnnotatedFunction> funcs;
	private Vector<String> retVars;

	public PGoAnnotationParser(Vector<PGoAnnotation> pGoAnnotations) throws PGoParseException {
		vars = new LinkedHashMap<String, AnnotatedVariable>();
		funcs = new LinkedHashMap<String, AnnotatedFunction>();
		retVars = new Vector<String>();

		for (PGoAnnotation annot : pGoAnnotations) {
			parseAnnote(annot);
		}
	}

	// Parses a single annotation
	private void parseAnnote(PGoAnnotation annot) throws PGoParseException {
		String[] parts = annot.getString().split("\\s");
		switch (parts[0].toLowerCase()) {
		case AnnotatedVariable.CONST:
		case AnnotatedVariable.ARG:
		case AnnotatedVariable.VAR:
			AnnotatedVariable av = AnnotatedVariable.parse(parts, annot.getLine());
			vars.put(av.getName(), av);
			break;
		case "func":
			AnnotatedFunction af = AnnotatedFunction.parse(parts, annot.getLine());
			funcs.put(af.getName(), af);
			break;
		case "ret":
			if (parts.length != 2) {
				throw new PGoParseException(
						"Annotation attribute \"ret\" expects argument <varname>. None provided", annot.getLine());
			}
			retVars.add(parts[1]);
			break;
		default:
			throw new PGoParseException("Unknown annotation attribute \"" + parts[0] + "\"", annot.getLine());
		}
	}

	// Returns all the annotated variables
	public ArrayList<AnnotatedVariable> getAnnotatedVariables() {
		// TODO Auto-generated method stub
		return null;
	}

	// Returns all the annotated functions
	public ArrayList<AnnotatedFunction> getAnnotatedFunctions() {
		// TODO Auto-generated method stub
		return null;
	}

}
