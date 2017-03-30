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

	LinkedHashMap<String, AnnotatedVariable> vars;
	LinkedHashMap<String, AnnotatedFunction> funcs;

	public PGoAnnotationParser(Vector<PGoAnnotation> pGoAnnotations) throws PGoParseException {
		vars = new LinkedHashMap<String, AnnotatedVariable>();
		funcs = new LinkedHashMap<String, AnnotatedFunction>();

		for (PGoAnnotation annot : pGoAnnotations) {
			parseAnnote(annot);
		}
	}

	// Parses a single annotation
	private void parseAnnote(PGoAnnotation annot) throws PGoParseException {
		String[] parts = annot.getString().split("\\s");
		switch (parts[0]) {
		case "const":
		case "arg":
			break;
		case "func":
			break;
		case "ret":
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
