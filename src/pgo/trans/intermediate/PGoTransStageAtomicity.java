package pgo.trans.intermediate;

import java.util.HashSet;
import java.util.Vector;

import pcal.AST;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoVariable;
import pgo.model.parser.AnnotatedLock;
import pgo.trans.PGoTransException;
import pgo.util.PcalASTUtil;

/**
 * Stage to detect concurrent accesses to variables and mark them as needing
 * thread safe.
 * 
 * TODO we can probably optimize this in terms of locking. Also need to deal
 * with networks
 *
 */
public class PGoTransStageAtomicity {

	// the intermediate data
	PGoTransIntermediateData data;

	public PGoTransStageAtomicity(PGoTransStageType s) throws PGoTransException {
		this.data = s.data;

		// If we have annotated whether we should lock, use the annotation.
		AnnotatedLock al = this.data.annots.getAnnotatedLock();
		if (al != null) {
			this.data.needsLock = al.needsLock();
			return;
		}

		// Mark all variables that have an assignment from processes as needing
		// to be atomic. We assume any variable that has an assignment within a
		// process to be accessed concurrently.

		for (PGoVariable v : this.data.globals.values()) {
			for (String pname : this.data.goroutines.keySet()) {
				// set of functions we already visited
				HashSet<String> visited = new HashSet<String>();

				PGoFunction prcs = this.data.funcs.get(pname);
				assert (prcs != null);
				Vector<AST> toExamine = new Vector<AST>();
				toExamine.addAll(prcs.getBody());

				Vector<String> funcsCalled = PcalASTUtil.collectFunctionCalls(toExamine);
				Vector<AST> newBodies = new Vector<AST>();
				while (!funcsCalled.isEmpty()) {
					visited.addAll(funcsCalled);

					for (String fname : funcsCalled) {
						newBodies.addAll(this.data.findPGoFunction(fname).getBody());
					}
					toExamine.addAll(newBodies);

					// TODO add tests for cases when this is needed
					// TODO add recursive cases (issue #7)
					funcsCalled = PcalASTUtil.collectFunctionCalls(newBodies);

					funcsCalled.removeAll(visited);

					newBodies.clear();
				}

				if (PcalASTUtil.containsAssignmentToVar(toExamine, v.getName())) {
					// assignment from a process means we need the variable
					// thread safe
					v.setAtomic(true);
					this.data.needsLock = true;
					break;
				}
			}
		}
	}
}
