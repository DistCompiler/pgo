package pgo.model.intermediate;

import java.util.List;

import pcal.AST.PVarDecl;
import pcal.AST.VarDecl;
import pcal.PcalParams;
import pcal.TLAExpr;
import pgo.model.parser.AnnotatedTLADefinition;
import pgo.model.parser.AnnotatedVariable.ArgAnnotatedVariable;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.TLAExprToType;
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeString;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;
import pgo.trans.PGoTransExpectedSingleExpressionException;
import pgo.trans.intermediate.PGoTempData;

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
	public static final String PROCESS_VAR_ARG = "self";

	// the name of the variable
	private String name;

	// whether the variable has a simple "=" assignment initialization
	private boolean isSimpleAssignInit;

	// the pluscal ast code block corresponding to variable initialization
	private TLAExpr tlaExpr;

	// the type of the variable
	private PGoType type;

	// The go syntax value
	private String goVal;

	// The line number in PlusCal
	private int line;

	// Whether this variable is a constant
	private boolean isConstant;

	// If this variable is initialized from command line argument, argInfo is
	// populated with the corresponding information of flagname, or position
	private ArgAnnotatedVariable argInfo;

	// Whether this variable needs atomic access (ie threadsafe)
	private boolean isAtomic;

	// the lock group id that this variable is associated with (-1 if no atomic
	// access needed)
	private int lockGroup;

	// whether we inferred the type of this variable or it was in an annotation
	private boolean inferred;

	// is this variable stored in the current process, or accessible via a request
	// to a remote server? A variable is only remote if it is global and we are
	// compiling a distributed algorithm
	private boolean remote;

	// hide the constructor. only construct through converting from VarDecl
	private PGoVariable(String n, PGoType tn) {
		name = n;
		type = tn;
		goVal = "";
		isConstant = false;
		inferred = false;
		argInfo = null;
		remote = false;
		lockGroup = -1;
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
		return goVal;
	}

	// Sets the value of this variable in go syntax
	public void setGoVal(String val) {
		this.goVal = val;
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

	public void setAtomic(boolean b) {
		this.isAtomic = b;
	}

	public boolean getIsAtomic() {
		return this.isAtomic;
	}

	public void setRemote(boolean isRemote) { this.remote = isRemote; }

	public boolean isRemote() { return this.remote; }

	public void setLockGroup(int group) {
		this.lockGroup = group;
	}

	public int getLockGroup() {
		return lockGroup;
	}

	public void setAsInferredType() {
		this.inferred = true;
	}

	public boolean wasInferred() {
		return inferred;
	}

	/**
	 * Converts a PlusCal AST variable into a basic PGoVariable intermediate
	 * representation. This does not create the variable initialization
	 * functions for Go and the type inference.
	 */
	public static PGoVariable convert(VarDecl var, PGoType tn) {
		PGoVariable r = new PGoVariable(var.var, tn);
		r.isSimpleAssignInit = var.isEq;
		r.tlaExpr = var.val;
		r.line = var.line;
		return r;
	}

	// The same as above but for a PVarDecl (for process variable)
	public static PGoVariable convert(PVarDecl var, PGoType tn) {
		PGoVariable r = new PGoVariable(var.var, tn);
		r.isSimpleAssignInit = var.isEq;
		r.tlaExpr = var.val;
		r.line = var.line;
		return r;
	}

	// The same as above but with a simple String
	public static PGoVariable convert(String var, PGoType tn) {
		PGoVariable r = new PGoVariable(var, tn);
		r.isSimpleAssignInit = true;
		r.tlaExpr = PcalParams.DefaultVarInit();
		r.line = -1;
		return r;
	}

	// Creates a variable representing the process id arguments for process functions
	public static PGoVariable processIdArg(PGoType tn) {
		return convert(PROCESS_VAR_ARG, tn);
	}

	// Creates a variable representing the IP:Port the process should bind when executing
	public static PGoVariable processNetAddress() {
		PGoVariable r = convert("ipAddr", PGoTypeString.getInstance());
		r.isSimpleAssignInit = false;
		return r;
	}

	// Creates a variable from a name and an initial value (a primitive),
	// inferring the type from the initial value.
	public static PGoVariable convert(String n, String val, PGoType tn) {
		PGoVariable r = new PGoVariable(n, tn);
		r.goVal = val;
		return r;
	}

	// Creates a variable based on a parameterless TLA definition
	public static PGoVariable convert(AnnotatedTLADefinition defn, PGoTempData varData) throws PGoTransException {
		if (!defn.getParams().isEmpty()) {
			throw new PGoTransException("Variable annotated as a function", defn.getLine());
		}
		// infer the type
		List<PGoTLAExpression> ptla = new TLAExprParser(defn.getExpr(), defn.getLine()).getResult();
		if (ptla.size() != 1) {
			throw new PGoTransExpectedSingleExpressionException(defn.getLine());
		}
		PGoVariable r = new PGoVariable(defn.getName(), new TLAExprToType(ptla.get(0), varData).getType());
		r.isSimpleAssignInit = true;
		r.tlaExpr = defn.getExpr();
		r.line = defn.getLine();
		return r;
	}

	@Override
	public boolean equals(Object other) {
		if (!(other instanceof PGoVariable)) {
			return false;
		}
		PGoVariable o = (PGoVariable) other;
		return getName().equals(o.getName());
	}
}
