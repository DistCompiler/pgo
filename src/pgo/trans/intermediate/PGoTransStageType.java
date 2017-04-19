package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.LinkedHashMap;

import pcal.AST.LabeledStmt;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoRoutineInit;
import pgo.model.intermediate.PGoVariable;
import pgo.model.parser.AnnotatedFunction;
import pgo.model.parser.AnnotatedVariable;
import pgo.parser.PGoAnnotationParser;
import pgo.parser.PGoParseException;
import pgo.parser.PcalParser.ParsedPcal;

/**
 * The second stage of the translation where we determine the types of all
 * variables and functions of the algorithm. This stage should end with all
 * variables' and functions' types being completely determined, otherwise a
 * PGoTransException will be thrown.
 *
 */
public class PGoTransStageType {

	// Whether the PlusCal program has multiple processes, or is just a single
	// threaded function
	private boolean isMultiProcess;

	// The algorithm name
	private String algName;

	// The global variables of this algorithm
	private LinkedHashMap<String, PGoVariable> globals;
	// The functions of this algorithm
	private LinkedHashMap<String, PGoFunction> funcs;

	// Array of code blocks we need to insert into the go main function
	private ArrayList<LabeledStmt> mainBlock;

	// Map of goroutines and its function to its initialization code
	private LinkedHashMap<String, PGoRoutineInit> goroutines;

	public PGoTransStageType(PGoTransStageOne s1, ParsedPcal pcal) throws PGoParseException {
		PGoAnnotationParser p = new PGoAnnotationParser(pcal.getPGoAnnotations());

		for (AnnotatedVariable v : p.getAnnotatedVariables()) {
			PGoVariable var = findPGoVariable(v.getName());
			if (var == null) {
				// TODO
			} else {
				v.fillVariable(var);
			}
		}
		
		for (AnnotatedFunction f : p.getAnnotatedFunctions()) {
			PGoFunction fun = findPGoFunction(f.getName());
			if (fun == null) {
				// TODO
			} else {
				f.fillFunction(fun);
			}
		}
	}

	private PGoFunction findPGoFunction(String name) {
		// TODO Auto-generated method stub
		return null;
	}

	// Find the PGoVariable of the given name from the program.
	private PGoVariable findPGoVariable(Object name) {
		// TODO Auto-generated method stub
		return null;
	}

}
