package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.LinkedHashMap;

import pcal.AST.LabeledStmt;
import pcal.TLAExpr;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoRoutineInit;
import pgo.model.intermediate.PGoVariable;

/**
 * This class holds all the important intermediate stage data and data
 * structures for each intermediate translation stage. Each stage will pass the
 * object to the next stage, adding information and modifying data with each
 * pass until the final go code generation stage.
 * 
 * This class and all members are package protected for access only within the
 * intermediate stage
 *
 */
class PGoTransIntermediateData {

	// Whether the PlusCal program has multiple processes, or is just a single
	// threaded function
	boolean isMultiProcess;

	// The algorithm name
	String algName;

	// The global variables of this algorithm
	LinkedHashMap<String, PGoVariable> globals;
	// The local variables we have yet to encountered from our passes (probably
	// hidden in a with clause)
	LinkedHashMap<String, PGoVariable> tempVars;
	// The functions of this algorithm
	LinkedHashMap<String, PGoFunction> funcs;

	// Defined TLAExpr to be parsed into functions. Except these are not of the
	// form individual functions, they are a collection of quick definitions. We
	// must individually parse these.
	// TODO support these
	TLAExpr tlaExpr;

	// Array of code blocks we need to insert into the go main function
	ArrayList<LabeledStmt> mainBlock;

	// Map of goroutines and its function to its initialization code
	LinkedHashMap<String, PGoRoutineInit> goroutines;

	PGoTransIntermediateData() {

		this.globals = new LinkedHashMap<String, PGoVariable>();
		this.tempVars = new LinkedHashMap<String, PGoVariable>();
		this.funcs = new LinkedHashMap<String, PGoFunction>();
		this.mainBlock = new ArrayList<LabeledStmt>();
		this.goroutines = new LinkedHashMap<String, PGoRoutineInit>();
	}

	// Finds the PGofunction of the given name, or null if none exists.
	// This method also takes care of finding functions prefixed by "PGo" in
	// cases of special functions defined in pluscal for predicates defined
	// outside the pluscal algorithm, and renaming them to without the PGo
	// prefix
	PGoFunction findPGoFunction(String name) {
		PGoFunction fun = funcs.get(name);
		if (fun == null) {
			fun = funcs.get("PGo" + name);
			if (fun == null) {
				return null;
			} else {
				// Change the PGo version of the function to the real name
				this.funcs.remove("PGo" + name);
				fun.setName(name);
				this.funcs.put(name, fun);
			}
		}
		return fun;
	}

	// Find the PGoVariable of the given name from the program.
	PGoVariable findPGoVariable(String name) {
		PGoVariable ret = null;
		if (name.contains(".")) {
			String[] parts = name.split("\\.");
			PGoFunction f = findPGoFunction(parts[0]);
			if (f != null) {
				ret = f.getVariable(parts[1]);
			}
		} else {
			ret = globals.get(name);
			if (ret == null) {
				for (PGoFunction f : funcs.values()) {
					ret = f.getVariable(name);
					if (ret != null) {
						break;
					}
				}
			}
		}

		return ret;
	}

}