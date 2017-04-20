package pgo.model.intermediate;

import pcal.AST.PVarDecl;
import pcal.AST.VarDecl;
import pcal.PcalParams;
import pcal.TLAExpr;
import pgo.model.intermediate.PGoType.PGoUndetermined;
import pgo.model.parser.AnnotatedVariable.ArgAnnotatedVariable;

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

	// whether the variable has a simple "=" assignment initialization
	private boolean isSimpleAssignInit;

	// the pluscal ast code block corresponding to variable initialization
	private TLAExpr tlaExpr;

	// the type of the variable
	private PGoType type;

	// The go syntax value
	private String goval;

	// The line number in pluscal
	private int line;

	// Whether this variable is a constant
	private boolean isConstant;

	// If this variable is initialized from command line argument, argInfo is
	// populated with the corresponding information of flagname, or position
	private ArgAnnotatedVariable argInfo;

	// private constructor. only construct through converting from VarDecl
	private PGoVariable() {
		type = new PGoUndetermined();
		goval = "";
		isConstant = false;
		argInfo = null;
	}

	public String getName() {
		return name;
	}

	public boolean getIsSimpleAssignInit() {
		return isSimpleAssignInit;
	}

	// Sets the simple assignment flag
	public void setIsSimpleAssign(boolean b) {
		this.isSimpleAssignInit = b;
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

	public String getGoVal() {
		return goval;
	}

	// Sets the value of this variable in go syntax
	public void setGoVal(String val) {
		this.goval = val;
	}

	public boolean getIsConstant() {
		return isConstant;
	}

	public void setIsConstant(boolean b) {
		this.isConstant = b;
	}

	public ArgAnnotatedVariable getArgInfo() {
		return argInfo;
	}

	public void setArgInfo(ArgAnnotatedVariable a) {
		this.argInfo = a;
	}

	public int getLine() {
		return line;
	}

	public void setLine(int line) {
		this.line = line;
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
		r.line = var.line;

		return r;
	}

	// The same as above but for a PVarDecl (for process variable)
	public static PGoVariable convert(PVarDecl var) {
		PGoVariable r = new PGoVariable();
		r.name = var.var;
		r.isSimpleAssignInit = var.isEq;
		r.tlaExpr = var.val;
		r.line = var.line;

		return r;
	}

	// The same as above but with a simple String
	public static PGoVariable convert(String var) {
		PGoVariable r = new PGoVariable();
		r.name = var;
		r.isSimpleAssignInit = true;
		r.tlaExpr = PcalParams.DefaultVarInit();
		r.line = -1;

		return r;
	}

	// Creates a variable representing the process id arguments for process
	// functions
	public static PGoVariable processIdArg() {
		PGoVariable r = new PGoVariable();
		r.name = "self";
		r.isSimpleAssignInit = true;
		r.tlaExpr = PcalParams.DefaultVarInit();
		r.line = -1;

		return r;
	}

	// Creates a variable from a name and the type of the variable
	public static PGoVariable convert(String n, PGoType tn) {
		PGoVariable r = new PGoVariable();
		r.name = n;
		r.isSimpleAssignInit = true;
		r.tlaExpr = PcalParams.DefaultVarInit();
		r.type = tn;
		r.line = -1;
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
		r.line = -1;
		return r;
	}

}
