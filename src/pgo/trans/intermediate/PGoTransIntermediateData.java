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
import pgo.model.intermediate.PGoVariable;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLADefinition;
import pgo.model.type.*;
import pgo.model.type.PGoType;
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

	public PGoTypeSolver solver;

	public PGoTypeGenerator typeGenerator;

	// Contains information for builtin TLA funcs like Len (length of tuple).
	private static final LinkedHashMap<String, PGoLibFunction> libFuncs = new LinkedHashMap<String, PGoLibFunction>() {
		{
			PGoTypeGenerator generator = new PGoTypeGenerator("b");
			put("Len", new PGoLibFunction("Len") {
				{
					addFuncSignature(Collections.singletonList(new PGoTypeSlice(generator.get())),
							"len",
							false,
							PGoTypeInt.getInstance());

					addFuncSignature(
							Collections.singletonList(new PGoTypeUnrealizedTuple()),
							"Size",
							true,
							PGoTypeInt.getInstance());

					addFuncSignature(Collections.singletonList(PGoTypeString.getInstance()),
							"len",
							false,
							PGoTypeInt.getInstance());
				}
			});

			put("Cardinality", new PGoLibFunction("Cardinality") {
				{
					addFuncSignature(Collections.singletonList(new PGoTypeSet(generator.get())),
							"Size",
							true,
							PGoTypeInt.getInstance());
				}
			});

			put("Append", new PGoLibFunction("Append") {
				{
					PGoType t = generator.get();
					addFuncSignature(
							Arrays.asList(new PGoTypeSlice(t), t),
							"append",
							false,
							new PGoTypeSlice(t));
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
	Map<TLAExprPgo, PGoTLAExpression> tlaToAST;

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
		globals = new LinkedHashMap<>();
		unresolvedVars = new LinkedHashMap<>();
		funcs = new LinkedHashMap<>();
		mainBlock = new Vector<>();
		goroutines = new LinkedHashMap<>();
		defns = new LinkedHashMap<>();
		needsLock = false;
		tlaToAST = new HashMap<>();
		labToLockGroup = new HashMap<>();
		numLockGroups = 0;
		cachedVarSet = new HashSet<>();
		solver = new PGoTypeSolver();
		typeGenerator = new PGoTypeGenerator("a");
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
	PGoTLAExpression findPGoTLA(TLAExpr t) {
		return tlaToAST.get(new TLAExprPgo(t));
	}

	// Put into the tlaToAST map
	void putPGoTLA(TLAExpr t, PGoTLAExpression tla) {
		tlaToAST.put(new TLAExprPgo(t), tla);
	}

}
