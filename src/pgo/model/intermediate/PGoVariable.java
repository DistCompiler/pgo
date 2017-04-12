package pgo.model.intermediate;

import pcal.AST.PVarDecl;
import pcal.AST.VarDecl;
import pgo.model.intermediate.PGoType.PGoUndetermined;
import pcal.PcalParams;
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

	// whether the variable has a simple "=" assignment initialization
	private boolean isSimpleAssignInit;

	// the pluscal ast code block corresponding to variable initialization
	private TLAExpr tlaExpr;

	// the type of the variable
	private PGoType type;

	// The go syntax value
	private String goval;

	// private constructor. only construct through converting from VarDecl
	private PGoVariable() {
		type = new PGoUndetermined();
		goval = "";
	}

	public String getName() {
		return name;
	}

	public boolean getIsSimpleAssignInit() {
		return isSimpleAssignInit;
	}

	public TLAExpr getPcalInitBlock() {
		return tlaExpr;
	}

	public PGoType getType() {
		return type;
	}

	public void setType(PGoType t) {
		type = t;
	}

	/**
	 * Converts a PlusCal AST variable into a basic PGoVariable intermediate
	 * representation. This does not create the variable initialization
	 * functions for Go and the type inference.
	 * 
	 * @param var
	 * @return
	 */
	public static PGoVariable convert(VarDecl var) {
		PGoVariable r = new PGoVariable();
		r.name = var.var;
		r.isSimpleAssignInit = var.isEq;
		r.tlaExpr = var.val;

		return r;
	}

	// The same as above but for a PVarDecl (for process variable)
	public static PGoVariable convert(PVarDecl var) {
		PGoVariable r = new PGoVariable();
		r.name = var.var;
		r.isSimpleAssignInit = var.isEq;
		r.tlaExpr = var.val;

		return r;
	}

	// The same as above but with a simple String
	public static PGoVariable convert(String var) {
		PGoVariable r = new PGoVariable();
		r.name = var;
		r.isSimpleAssignInit = true;
		r.tlaExpr = PcalParams.DefaultVarInit();

		return r;
	}

	// Creates a variable representing the process id arguments for process
	// functions
	public static PGoVariable processIdArg() {
		PGoVariable r = new PGoVariable();
		r.name = "self";
		r.isSimpleAssignInit = true;
		r.tlaExpr = PcalParams.DefaultVarInit();

		return r;
	}

	// Creates a variable from a name and the type of the variable
	public static PGoVariable convert(String n, PGoType tn) {
		PGoVariable r = new PGoVariable();
		r.name = n;
		r.isSimpleAssignInit = true;
		r.tlaExpr = PcalParams.DefaultVarInit();
		r.type = tn;
		return r;
	}

	// Creates a variable from a name and an initial value (a primitive),
	// inferring the type from the initial value.
	public static PGoVariable convert(String n, String val, PGoType tn) {
		PGoVariable r = new PGoVariable();
		r.name = n;
		r.isSimpleAssignInit = true;
		r.goval = val;
		r.type = tn;
		return r;
	}

}
