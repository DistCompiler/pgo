package pgo.trans.intermediate;

import java.util.Collection;
import java.util.HashMap;
import java.util.Vector;

import pcal.AST;
import pcal.AST.Macro;
import pcal.AST.Multiprocess;
import pcal.AST.Procedure;
import pcal.AST.Uniprocess;
import pcal.AST.VarDecl;
import pcal.TLAExpr;
import pgo.trans.PGoTransException;
import pgo.trans.intermediate.model.PGoFunction;
import pgo.trans.intermediate.model.PGoVariable;

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
	private HashMap<String, PGoVariable> globals;
	// The functions of this algorithm
	private HashMap<String, PGoFunction> funcs;

	// Defined TLAExpr to be parsed into functions. Except these are not of the
	// form individual functions, they are a collection of quick definitions. We
	// must individually parse these.
	private TLAExpr tlaExpr;

	public PGoTransStageOne(AST ast) throws PGoTransException {
		this.ast = ast;
		this.globals = new HashMap<String, PGoVariable>();
		trans();
	}

	public boolean getIsMultiProcess() {
		return isMultiProcess;
	}

	public String getAlgName() {
		return algName;
	}

	public Collection<PGoVariable> getGlobals() {
		return globals.values();
	}

	public PGoVariable getGlobal(String name) {
		return globals.get(name);
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
		// TODO the unique parts
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
		// TODO the unique parts

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
