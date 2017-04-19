package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.Vector;

import pcal.AST;
import pcal.AST.LabeledStmt;
import pcal.AST.Macro;
import pcal.AST.Multiprocess;
import pcal.AST.Procedure;
import pcal.AST.Process;
import pcal.AST.Uniprocess;
import pcal.AST.VarDecl;
import pcal.TLAExpr;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoRoutineInit;
import pgo.model.intermediate.PGoVariable;
import pgo.parser.PcalParser.ParsedPcal;
import pgo.trans.PGoTransException;

/**
 * Makes initial pass over the AST to generate the basic intermediate
 * structures, which may not be fully populated (ie, type inference is not
 * completed).
 *
 */
public class PGoTransStageOne {

	// The PlusCal AST to parse
	private AST ast;

	// Whether the PlusCal program has multiple processes, or is just a single
	// threaded function
	private boolean isMultiProcess;

	// The algorithm name
	private String algName;

	// The global variables of this algorithm
	private LinkedHashMap<String, PGoVariable> globals;
	// The functions of this algorithm
	private LinkedHashMap<String, PGoFunction> funcs;

	// Defined TLAExpr to be parsed into functions. Except these are not of the
	// form individual functions, they are a collection of quick definitions. We
	// must individually parse these.
	// TODO support these
	private TLAExpr tlaExpr;

	// Array of code blocks we need to insert into the go main function
	private ArrayList<LabeledStmt> mainBlock;

	// Map of goroutines and its function to its initialization code
	private LinkedHashMap<String, PGoRoutineInit> goroutines;

	public PGoTransStageOne(ParsedPcal parsed) throws PGoTransException {
		this.ast = parsed.getAST();
		this.globals = new LinkedHashMap<String, PGoVariable>();
		this.funcs = new LinkedHashMap<String, PGoFunction>();
		this.mainBlock = new ArrayList<LabeledStmt>();
		this.goroutines = new LinkedHashMap<String, PGoRoutineInit>();
		trans();
	}

	public boolean getIsMultiProcess() {
		return isMultiProcess;
	}

	public String getAlgName() {
		return algName;
	}

	public ArrayList<PGoVariable> getGlobals() {
		return new ArrayList<PGoVariable>(globals.values());
	}

	public PGoVariable getGlobal(String name) {
		return globals.get(name);
	}

	public ArrayList<PGoFunction> getFunctions() {
		return new ArrayList<PGoFunction>(funcs.values());
	}

	public PGoFunction getFunction(String name) {
		return funcs.get(name);
	}

	public ArrayList<LabeledStmt> getMain() {
		return mainBlock;
	}

	public ArrayList<PGoRoutineInit> getGoRoutineInits() {
		return new ArrayList<PGoRoutineInit>(goroutines.values());
	}

	public PGoRoutineInit getGoRoutineInit(String r) {
		return goroutines.get(r);
	}

	/**
	 * Translates the PlusCal AST to the first stage intermediate representation
	 * 
	 * @throws PGoTransException
	 *             on error
	 */
	private void trans() throws PGoTransException {
		if (ast instanceof Uniprocess) {
			isMultiProcess = false;
			trans((Uniprocess) ast);
		} else if (ast instanceof Multiprocess) {
			isMultiProcess = true;
			trans((Multiprocess) ast);
		} else {
			throw new PGoTransException("Error: PlusCal algorithm must be one of uniprocess or multiprocess");
		}
	}

	/**
	 * Class for Multiprocess AST and Uniprocess AST that creates a common way
	 * of operating on them. This class will keep all the common fields of the
	 * Multiprocess and Uniprocess AST
	 * 
	 */
	private class BaseAlgAST extends AST {

		public String name = "";
		public Vector decls = null; // of VarDecl
		public TLAExpr defs = null;
		public Vector macros = null; // of Macro
		public Vector prcds = null; // of Procedure

		public BaseAlgAST(Multiprocess ast) {
			this.name = ast.name;
			this.decls = ast.decls;
			this.defs = ast.defs;
			this.macros = ast.macros;
			this.prcds = ast.prcds;
		}

		public BaseAlgAST(Uniprocess ast) {
			this.name = ast.name;
			this.decls = ast.decls;
			this.defs = ast.defs;
			this.macros = ast.macros;
			this.prcds = ast.prcds;
		}
	}

	/**
	 * Translates the PlusCal AST of a multiprocess algorithm into first stage
	 * intermediate representation, setting the corresponding fields of this
	 * class
	 * 
	 * @param ast
	 */
	private void trans(Multiprocess ast) {
		transCommon(new BaseAlgAST(ast));

		// TODO eventually we want to support a process as a goroutine and a
		// networked process. For now we just do goroutines
		for (Process p : (Vector<Process>) ast.procs) {
			PGoFunction f = PGoFunction.convert(p);
			funcs.put(f.getName(), f);

			goroutines.put(f.getName(), PGoRoutineInit.convert(p));
		}
	}

	/**
	 * Translates the PlusCal AST of a uniprocess algorithm into first stage
	 * intermediate representation, setting the corresponding fields of this
	 * class
	 * 
	 * @param ast
	 */
	private void trans(Uniprocess ast) {
		transCommon(new BaseAlgAST(ast));

		mainBlock.addAll(ast.body);
	}

	/**
	 * Translates the common parts of Multiprocess and Uniprocess (called now BaseAST)
	 * PlusCal algorithm into first stage intermediate representation, setting the
	 * corresponding fields of this class.
	 * 
	 * Common parts are: name, variable declarations, tla definitions, and
	 * macros, procedures
	 * 
	 * @param ast
	 *            BaseAlgAST representation of types Uniprocess or Multiprocess
	 */
	private void transCommon(BaseAlgAST ast) {
		this.algName = ast.name;
		for (VarDecl var : (Vector<VarDecl>) ast.decls) {
			PGoVariable pvar = PGoVariable.convert(var);
			globals.put(pvar.getName(), pvar);
		}
		this.tlaExpr = ast.defs;
		for (Macro m : (Vector<Macro>) ast.macros) {
			PGoFunction f = PGoFunction.convert(m);
			funcs.put(f.getName(), f);
		}
		for (Procedure m : (Vector<Procedure>) ast.prcds) {
			PGoFunction f = PGoFunction.convert(m);
			funcs.put(f.getName(), f);
		}
	}

}
