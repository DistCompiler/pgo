package pgo.trans.intermediate.model;

import pcal.AST.PVarDecl;
import pcal.AST.VarDecl;
import pcal.TLAExpr;

/**
 * Intermediate representation of a single pluscal and golang variable.
 * 
 * PlusCal declares variables as `variable varname=val; varname2=val2;
 * varname3...` and may include PlusCal specific syntax initialization. GoLang
 * declares variables as `type var;` or `type var = val;` or more complex
 * initializations
 *
 */
public class PGoVariable {
	// the name of the variable
	private String name;

	// TODO types, initialization, etc

	// whether the variable is assigned = or \in
	private boolean isEq;

	// the pluscal ast code block corresponding to variable initialization
	private TLAExpr tlaExpr;

	// private constructor. only construct through converting from VarDecl
	private PGoVariable() {
	}

	public String getName() {
		return name;
	}

	public TLAExpr getPcalInitBlock() {
		return tlaExpr;
	}

	/**
	 * Converts a PlusCal AST variable into a basic PGoVariable intermediate
	 * representation. This does not create the variable initilization functions
	 * for Go and the type inference.
	 * 
	 * @param var
	 * @return
	 */
	public static PGoVariable convert(VarDecl var) {
		PGoVariable r = new PGoVariable();
		r.name = var.var;
		r.isEq = var.isEq;
		r.tlaExpr = var.val;

		return r;
	}

	// The same as above but for a PVarDecl (for process variable)
	public static PGoVariable convert(PVarDecl var) {
		PGoVariable r = new PGoVariable();
		r.name = var.var;
		r.isEq = var.isEq;
		r.tlaExpr = var.val;

		return r;
	}
}
