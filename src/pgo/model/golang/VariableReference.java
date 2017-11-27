package pgo.model.golang;

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

	private static final String GLOBAL_STATE = PGoTransStageGoGen.GLOBAL_STATE_OBJECT;

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

		// the function to be invoked on the global state manager
		String fn = "";

		// if the variable is remote, generate the corresponding call to the global
		// state manager to retrieve the variable name
		if (var.isRemote()) {
			if (var.getType() instanceof PGoPrimitiveType.PGoInt)
				fn = "GetInt";

			else if (var.getType() instanceof PGoPrimitiveType.PGoString)
				fn = "GetString";

			else if (var.getType() instanceof PGoCollectionType.PGoSlice) {
				switch (var.getType().toString()) {
					case "[]int":
						fn = "GetIntCollection";
						break;
					case "[]string":
						fn = "GetStringCollection";
						break;
					default:
						assert(false);
				}

			}

			else {
				// should not be reachable - variable type is not supported
				assert(false);
			}

			ret.add(String.format("%s.%s(\"%s\")", GLOBAL_STATE, fn, var.getName()));

		} else {
			// if the variable is not remote, just use the variable name itself
			ret.add(var.getName());
		}
		return ret;
	}
}
