package pgo.parser;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.Vector;

import pgo.model.parser.AnnotatedFunction;
import pgo.model.parser.AnnotatedLock;
import pgo.model.parser.AnnotatedProcess;
import pgo.model.parser.AnnotatedReturnVariable;
import pgo.model.parser.AnnotatedTLADefinition;
import pgo.model.parser.AnnotatedVariable;
import pgo.model.parser.PGoAnnotation;

/**
 * Parses the annotations of the pluscal algorithm for pgo
 *
 */
public class PGoAnnotationParser {

	private static final String FUNC_KW = "func";
	private static final String RET_KW = "ret";
	private static final String PROC_KW = "proc";
	private static final String DEF_KW = "def";
	private static final String LOCK_KW = "lock";

	private LinkedHashMap<String, AnnotatedVariable> vars;
	private LinkedHashMap<String, AnnotatedFunction> funcs;
	private LinkedHashMap<String, AnnotatedProcess> procs;
	private LinkedHashMap<String, AnnotatedReturnVariable> retVars;
	private LinkedHashMap<String, AnnotatedTLADefinition> defns;
	// null if there is no lock annotation
	private AnnotatedLock lock;

	public PGoAnnotationParser(Vector<PGoAnnotation> pGoAnnotations) throws PGoParseException {
		vars = new LinkedHashMap<String, AnnotatedVariable>();
		funcs = new LinkedHashMap<String, AnnotatedFunction>();
		procs = new LinkedHashMap<String, AnnotatedProcess>();
		retVars = new LinkedHashMap<String, AnnotatedReturnVariable>();
		defns = new LinkedHashMap<>();
		lock = null;

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
		case FUNC_KW:
			AnnotatedFunction af = AnnotatedFunction.parse(parts, annot.getLine());
			funcs.put(af.getName(), af);
			break;
		case RET_KW:
			AnnotatedReturnVariable ar = AnnotatedReturnVariable.parse(parts, annot.getLine());
			retVars.put(ar.getName(), ar);
			break;
        case PROC_KW:
			AnnotatedProcess ap = AnnotatedProcess.parse(parts, annot.getLine());
			procs.put(ap.getName(), ap);
			break;
        case DEF_KW:
			AnnotatedTLADefinition ad = AnnotatedTLADefinition.parse(annot.getString(), annot.getLine());
			defns.put(ad.getName(), ad);
			break;
        case LOCK_KW:
			if (lock != null) {
				throw new PGoParseException("Found more than one lock annotation", annot.getLine());
			}
			lock = AnnotatedLock.parse(parts, annot.getLine());
			break;
		default:
			throw new PGoParseException("Unknown annotation attribute \"" + parts[0] + "\"", annot.getLine());
		}
	}

	public AnnotatedVariable getAnnotatedVariable(String name) {
		return vars.get(name);
	}

	// Returns all the annotated variables
	public ArrayList<AnnotatedVariable> getAnnotatedVariables() {
		return new ArrayList<AnnotatedVariable>(vars.values());
	}

	public AnnotatedFunction getAnnotatedFunction(String name) {
		return funcs.get(name);
	}

	// Returns all the annotated functions
	public ArrayList<AnnotatedFunction> getAnnotatedFunctions() {
		return new ArrayList<AnnotatedFunction>(funcs.values());
	}

	// Returns all the return variables
	public ArrayList<AnnotatedReturnVariable> getReturnVariables() {
		return new ArrayList<AnnotatedReturnVariable>(retVars.values());
	}

	public AnnotatedReturnVariable getReturnVariable(String name) {
		return retVars.get(name);
	}

	// Returns all the annotated processes
	public ArrayList<AnnotatedProcess> getAnnotatedProcesses() {
		return new ArrayList<AnnotatedProcess>(procs.values());
	}

	public AnnotatedProcess getAnnotatedProcess(String name) {
		return procs.get(name);
	}

	public ArrayList<AnnotatedTLADefinition> getAnnotatedTLADefinitions() {
		return new ArrayList<>(defns.values());
	}

	public AnnotatedTLADefinition getAnnotatedTLADefinition(String name) {
		return defns.get(name);
	}

	public AnnotatedLock getAnnotatedLock() {
		return lock;
	}
}
