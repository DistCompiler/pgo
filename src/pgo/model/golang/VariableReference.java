package pgo.model.golang;

import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoVariable;

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

	public VariableReference(String name, PGoVariable var) {
		this.name = name;
		this.var = var;
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
		if (var.isRemote()) {
			if (var.getType() instanceof PGoPrimitiveType.PGoInt)
				ret.add(String.format("globalState.GetInt(\"%s\")", var.getName()));
			else if (var.getType() instanceof PGoPrimitiveType.PGoString) {
				ret.add(String.format("globalState.GetString(\"%s\")", var.getName()));
			} else {
				// should not be reachable - variable type is not supported
				assert(false);
			}
		} else {
			ret.add(var.getName());
		}
		return ret;
	}
}
