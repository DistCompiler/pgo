package pgo.trans.intermediate.model;

import java.util.HashMap;

import pcal.AST.Macro;
import pcal.AST.Procedure;

/**
 * Intermediate representation of a single pluscal and golang function.
 * 
 * PlusCal declares functions as macros, procedures, and TLAExpr (for boolean
 * outputs) Intermediate representation parses out the basic information without
 * fully converting to go
 *
 */
public class PGoFunction {

	// The function name
	private String funcName = "";

	// The parameters to the function
	private HashMap<String, PGoVariable> params;

	// The declared variables of the function
	private HashMap<String, PGoVariable> vars;

	public String getName() {
		return funcName;
	}

	public static PGoFunction convert(Procedure m) {
		// TODO Auto-generated method stub
		return new PGoFunction();
	}

	public static PGoFunction convert(Macro m) {
		// TODO Auto-generated method stub
		return new PGoFunction();
	}

}
