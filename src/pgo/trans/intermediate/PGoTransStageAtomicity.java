package pgo.trans.intermediate;

import java.util.HashSet;
import java.util.Vector;

import pcal.AST;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoVariable;
import pgo.parser.PGoParseException;
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
public class PGoTransStageAtomicity extends PGoTransStageBase {

	public PGoTransStageAtomicity(PGoTransStageType s) throws PGoParseException, PGoTransException {
		super(s);

		// Mark all variables that have an assignment from processes as needing
		// to be atomic. We assume any variable that has an assignment within a
		// process to be accessed concurrently.

		for (PGoVariable v : this.intermediateData.globals.values()) {
			for (String pname : this.intermediateData.goroutines.keySet())
			{
				// set of functions we already visited
				HashSet<String> visited = new HashSet<String>();
				
				PGoFunction prcs = this.intermediateData.funcs.get(pname);
				assert (prcs != null);
				Vector<AST> toExamine = new Vector<AST>();
				toExamine.addAll(prcs.getBody());

				Vector<String> funcsCalled = PcalASTUtil.collectFunctionCalls(toExamine);
				Vector<AST> newBodies = new Vector<AST>();
				while (!funcsCalled.isEmpty()) {
					visited.addAll(funcsCalled);

					for (String fname : funcsCalled) {
						newBodies.addAll(this.intermediateData.findPGoFunction(fname).getBody());
					}
					toExamine.addAll(newBodies);

					// TODO add tests for cases when this is needed
					// TODO add recursive cases
					funcsCalled = PcalASTUtil.collectFunctionCalls(newBodies);

					funcsCalled.removeAll(visited);

					newBodies.clear();
				}

				if (PcalASTUtil.containsAssignmentToVar(toExamine, v.getName())) {
					// assignment from a process means we need the variable
					// thread safe
					v.setAtomic(true);
					break;
				}
			}
		}
	}
}
