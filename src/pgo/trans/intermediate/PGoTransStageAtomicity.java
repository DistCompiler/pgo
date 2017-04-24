package pgo.trans.intermediate;

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

		for (PGoVariable v : this.intermediateData.globals.values()) {
			for (String pname : this.intermediateData.goroutines.keySet()) {
				PGoFunction prcs = this.intermediateData.funcs.get(pname);
				assert (prcs != null);
				Vector<AST> toExamine = new Vector<AST>();
				toExamine.addAll(prcs.getBody());

				Vector<String> funcsCalled = PcalASTUtil.collectFunctionCalls(toExamine);
				Vector<AST> newBodies = new Vector<AST>();
				while (!funcsCalled.isEmpty()) {
					for (String fname : funcsCalled) {
						newBodies.addAll(this.intermediateData.findPGoFunction(fname).getBody());
					}
					toExamine.addAll(newBodies);
					PcalASTUtil.collectFunctionCalls(newBodies);
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
