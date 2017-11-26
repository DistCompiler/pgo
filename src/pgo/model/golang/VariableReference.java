package pgo.model.golang;

import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoType;
import pgo.model.intermediate.PGoVariable;

import java.util.HashMap;
import java.util.Map;
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
	private PGoVariable var;

	public VariableReference(PGoVariable var) {
		this.var = var;
	}

	@Override
	public Vector<String> toGo() {
		Vector<String> ret = new Vector<>();
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
