package pgo.trans.intermediate;

import java.util.*;

import pcal.AST;
import pcal.AST.LabeledStmt;
import pcal.TLAExpr;
import pcal.TLAExprPgo;
import pgo.PGoNetOptions;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoLibFunction;
import pgo.model.intermediate.PGoRoutineInit;
import pgo.model.intermediate.PGoType;
import pgo.model.intermediate.PGoVariable;
import pgo.model.tla.PGoTLA;
import pgo.model.tla.PGoTLADefinition;
import pgo.parser.PGoAnnotationParser;

/**
 * This class holds all the important intermediate stage data and data
 * structures for each intermediate translation stage. Each stage will pass the
 * object to the next stage, adding information and modifying data with each
 * pass until the final go code generation stage.
 * 
 * This class and all members are package protected for access only within the
 * intermediate stage
 *
 */
class PGoTransIntermediateData {

	// The PlusCal AST
	AST ast;

	// Whether the PlusCal program has multiple processes, or is just a single
	// threaded function
	boolean isMultiProcess;

	// The algorithm name
	String algName;

	// The global variables of this algorithm
	LinkedHashMap<String, PGoVariable> globals;
	// The local variables we have yet to encountered from our passes (probably
	// hidden in a with clause)
	LinkedHashMap<String, PGoVariable> unresolvedVars;
	// The functions of this algorithm
	LinkedHashMap<String, PGoFunction> funcs;
	// The TLA function definitions
	LinkedHashMap<String, PGoTLADefinition> defns;

	// This tracks which remote variables are cached locally for processing
	public HashSet<PGoVariable> cachedVarSet;

	// Contains information for builtin TLA funcs like Len (length of tuple).
	private static final LinkedHashMap<String, PGoLibFunction> libFuncs = new LinkedHashMap<String, PGoLibFunction>() {
		{
			put("Len", new PGoLibFunction("Len") {
				{
					addFuncSignature(
							new Vector<PGoType>() {
								{
									add(PGoType.inferFromGoTypeName("[]E"));
								}
							},
							"len",
							false,
							PGoType.inferFromGoTypeName("int"));

					addFuncSignature(
							new Vector<PGoType>() {
								{
									add(PGoType.inferFromGoTypeName("tuple[E]"));
								}
							},
							"Size",
							true,
							PGoType.inferFromGoTypeName("int"));

					addFuncSignature(
							new Vector<PGoType>() {
								{
									add(PGoType.inferFromGoTypeName("string"));
								}
							},
							"len",
							false,
							PGoType.inferFromGoTypeName("int"));
				}
			});

			put("Cardinality", new PGoLibFunction("Cardinality") {
				{
					addFuncSignature(
							new Vector<PGoType>() {
								{
									add(PGoType.inferFromGoTypeName("set[E]"));
								}
							},
							"Size",
							true,
							PGoType.inferFromGoTypeName("int"));
				}
			});

			put("Append", new PGoLibFunction("Append") {
				{
					addFuncSignature(
							new Vector<PGoType>() {
								{
									add(PGoType.inferFromGoTypeName("[]E"));
									add(PGoType.inferFromGoTypeName("E"));
								}
							},
							"append",
							false,
							PGoType.inferFromGoTypeName("[]E"));
				}
			});
		}
	};

	// Defined TLAExpr to be parsed into functions. Except these are not of the
	// form individual functions, they are a collection of quick definitions. We
	// must individually parse these.
	// TODO support these
	TLAExpr tlaExpr;

	// Array of code blocks we need to insert into the go main function
	Vector<LabeledStmt> mainBlock;

	// Map of goroutines and its function to its initialization code
	LinkedHashMap<String, PGoRoutineInit> goroutines;

	// The annotation information
	PGoAnnotationParser annots;

	// Whether we need a lock in this algorithm
	boolean needsLock;

	// Maps all TLAExprs found in the ast to their corresponding PGoTLA
	// representation
	Map<TLAExprPgo, PGoTLA> tlaToAST;

	// Maps the label name to the lock group that should be used when entering
	// the label (-1 if none is needed)
	Map<String, Integer> labToLockGroup;
	// the number of lock groups there are
	int numLockGroups;
	public PGoNetOptions netOpts;

	public static PGoTransIntermediateData buildWith(PGoNetOptions networkOptions) {
		PGoTransIntermediateData ret = new PGoTransIntermediateData();
		ret.netOpts = networkOptions;
		return ret;
	}

	PGoTransIntermediateData() {

		this.globals = new LinkedHashMap<>();
		this.unresolvedVars = new LinkedHashMap<>();
		this.funcs = new LinkedHashMap<>();
		this.mainBlock = new Vector<>();
		this.goroutines = new LinkedHashMap<>();
		this.defns = new LinkedHashMap<>();
		this.needsLock = false;
		this.tlaToAST = new HashMap<>();
		this.labToLockGroup = new HashMap<>();
		this.numLockGroups = 0;
		this.cachedVarSet = new HashSet<>();

	}

	// Finds the PGofunction of the given name, or null if none exists.
	PGoFunction findPGoFunction(String name) {
		return funcs.get(name);
	}

	// Find the PGoVariable of the given name from the program.
	PGoVariable findPGoVariable(String name) {
		PGoVariable ret = null;
		if (name.contains(".")) {
			String[] parts = name.split("\\.");
			PGoFunction f = findPGoFunction(parts[0]);
			if (f != null) {
				ret = f.getVariable(parts[1]);
			}
		} else {
			ret = globals.get(name);
			if (ret == null) {
				for (PGoFunction f : funcs.values()) {
					ret = f.getVariable(name);
					if (ret != null) {
						break;
					}
				}
			}
			if (ret == null) {
				ret = unresolvedVars.get(name);
			}
		}

		return ret;
	}

	// Return the TLA definition with the given name.
	PGoTLADefinition findTLADefinition(String name) {
		return defns.get(name);
	}

	// Return the TLA library function with the given name and parameters
	PGoLibFunction findBuiltinFunction(String name) {
		return libFuncs.get(name);
	}

	// Find the PGoTLA corresponding to the TLA expression
	PGoTLA findPGoTLA(TLAExpr t) {
		return tlaToAST.get(new TLAExprPgo(t));
	}

	// Put into the tlaToAST map
	void putPGoTLA(TLAExpr t, PGoTLA tla) {
		tlaToAST.put(new TLAExprPgo(t), tla);
	}

}
