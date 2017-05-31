package pgo.trans.intermediate;

import java.util.LinkedHashMap;
import java.util.Map;

import pgo.model.intermediate.PGoVariable;

/**
 * A class that holds the same data as the PGoTransIntermediateData, in addition
 * to variables that are local to some scope (e.g. in a with clause or set
 * declaration). Intended for use in the TLAExprToType class, when inferring
 * expressions like x*y : x \in S, y \in T.
 *
 */
public class PGoTempData extends PGoTransIntermediateData {
	// The local variables
	private LinkedHashMap<String, PGoVariable> locals;

	public PGoTempData(PGoTransIntermediateData data) {
		isMultiProcess = data.isMultiProcess;
		algName = data.algName;
		// don't need to make deep copy since we can't mess with these fields
		// anyway
		globals = data.globals;
		unresolvedVars = data.unresolvedVars;
		funcs = data.funcs;
		tlaExpr = data.tlaExpr;
		mainBlock = data.mainBlock;
		goroutines = data.goroutines;
		annots = data.annots;
		needsLock = data.needsLock;
		locals = new LinkedHashMap<>();
	}
	
	public Map<String, PGoVariable> getLocals() {
		return locals;
	}
	
	public PGoVariable findPGoVariable(String name) {
		PGoVariable ret = super.findPGoVariable(name);
		if (ret == null || locals.containsKey(name)) {
			ret = locals.get(name);
		}
		return ret;
	}
}
