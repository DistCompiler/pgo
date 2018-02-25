package pgo.model.golang;

import pgo.model.distsys.StateStrategy;
import pgo.model.intermediate.PGoCollectionType;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoVariable;
import pgo.trans.intermediate.PGoTransStageGoGen;

import java.util.Vector;

/**
 * Represents a reference to a variable (local or global). In most cases,
 * referencing a PlusCal variable generates code to access a Go variable
 * of the same name.
 *
 * However, for globally managed variables (global state in distributed
 * applications), the code generated accesses the state server (etcd) to
 * retrieve the current value of a variable.
 *
 */
public class VariableReference extends Statement {
	// the variable name
	private String name;

	// the reference to the variable (might not exist when declaring a local variable)
	private PGoVariable var;

	// whether this variable is cached locally
	private boolean cachedLocally;

	private StateStrategy stateStrategy;

	public VariableReference(String name, PGoVariable var, boolean isCachedLocally, StateStrategy stateStrategy) {
		this.name = name;
		this.var = var;
		this.cachedLocally = isCachedLocally;
		this.stateStrategy = stateStrategy;
	}

	@Override
	public Vector<String> toGo() {
		Vector<String> ret = new Vector<>();
		// if the variable is not previously known, return its name
		// (first reference to a local variable)
		if (var == null) {
			ret.add(name);
			return ret;
		}

		// if the variable is remote, generate the corresponding call to the global
		// state manager to retrieve the variable name
		//
		// we only issue a call to the state manager in case the variable is not
		// `cachedLocally' -- in that case, variable access is happening inside
		// a distributed lock, and the state of the variables will be pushed to
		// the state manager once the lock is released (i.e., implementing
		// something similar to transaction semantics)
		if (var.isRemote() && !cachedLocally) {
			ret.add(stateStrategy.getVar(var));
		} else {
			// if the variable is not remote, just use the variable name itself
			ret.add(var.getName());
		}
		return ret;
	}
}
