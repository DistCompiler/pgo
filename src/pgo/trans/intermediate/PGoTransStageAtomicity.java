package pgo.trans.intermediate;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Vector;

import pcal.AST.Clause;
import pcal.AST.LabelEither;
import pcal.AST.LabelIf;
import pcal.AST.LabeledStmt;
import pcal.AST.SingleAssign;
import pgo.model.intermediate.PGoCollectionType;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoVariable;
import pgo.model.parser.AnnotatedLock;
import pgo.trans.PGoTransException;
import pgo.util.PcalASTUtil;

/**
 * Stage to detect concurrent accesses to variables and mark them as needing
 * thread safe.
 * 
 * The current behaviour is to group variables together and guard each group
 * with a lock. Two variables are in the same group if they can be accessed in
 * the same label.
 * 
 * This stage determines the value of needsLock, fills the lockGroup field of
 * all global PGoVariables, and populates the labToLockGroup method.
 *
 */
public class PGoTransStageAtomicity {

	// the intermediate data
	PGoTransIntermediateData data;

	public PGoTransStageAtomicity(PGoTransStageType s) throws PGoTransException {
		this.data = s.data;

		// If we have annotated whether we should lock, use the annotation.
		AnnotatedLock al = this.data.annots.getAnnotatedLock();
		if (al != null) {
			this.data.needsLock = al.needsLock();
			if (!this.data.needsLock) {
				return;
			}
		} else if (!this.data.isMultiProcess) {
			this.data.needsLock = false;
			return;
		}

		inferAtomic();
	}

	// a variable is serializable if it can be maintained remotely if networking
	// is enabled.
	//
	// See the `pgo/distsys' implementation for more details.
	private boolean isSerializable(PGoVariable var) {
	    Vector<String> allowedCollections = new Vector<String>() {
			{
				add("[]int");
				add("[]string");
			}
		};

		if (var.getType() instanceof PGoPrimitiveType.PGoInt) {
			return true;
		}

		if (var.getType() instanceof PGoPrimitiveType.PGoString) {
			return true;
		}

		// Collection types are only supported if they are of one of the allowed types.
		// There is a correspondence here between what types are allowed and what types
		// the `pgo/distsys' Go package supports. The lists should be in sync.
		if (var.getType() instanceof PGoCollectionType.PGoSlice &&
				allowedCollections.contains(var.getType().toString())) {
		    return true;
		}

		return false;
	}

	// Infer the locking groups that the variables belong to.
	private void inferAtomic() throws PGoTransException {
		// this will group variables that may be accessed in a single label
		DisjointSets dsu = new DisjointSets();
		// the result maps the label name to the variables that are accessed in
		// it
		PcalASTUtil.Walker<Map<String, Set<PGoVariable>>> walker = new PcalASTUtil.Walker<Map<String, Set<PGoVariable>>>() {
			// the current label we are in
			String curLabel;

			@Override
			protected void init() {
				result = new HashMap<>();
			}

			@Override
			protected void visit(LabeledStmt ls) throws PGoTransException {
				curLabel = ls.label;
				result.put(curLabel, new HashSet<>());
				super.visit(ls);
			}

			@Override
			protected void visit(SingleAssign sa) throws PGoTransException {
				// we only care about global variables, so don't use
				// findPGoVariable

				PGoVariable toInsert = data.globals.get(sa.lhs.var);
				if (toInsert != null) {
					result.get(curLabel).add(toInsert);
					toInsert.setAtomic(true);
					toInsert.setRemote(data.netOpts.isEnabled());

					// if our global variable is to be stored remotely, but is not of a
					// supported type, abort compilation
					if (toInsert.isRemote() && !isSerializable(toInsert)) {
						String desc = String.format("Remote variable %s is not serializable (type %s)",
								toInsert.getName(), toInsert.getType().getClass().getName());
						throw new PGoTransException(desc);
					}
				}
			}

			@Override
			protected void visit(LabelIf lif) throws PGoTransException {
				// we might hit some labels in the "then" block, but the "else"
				// block will be in the old label
				String oldLabel = curLabel;
				walk(lif.unlabThen);
				walk(lif.labThen);
				// reset to old label before walking else
				curLabel = oldLabel;
				walk(lif.unlabElse);
				walk(lif.labElse);
				// there has to be a label after a LabelIf, so don't need to
				// worry about anything here
			}

			@Override
			protected void visit(LabelEither le) throws PGoTransException {
				String oldLabel = curLabel;
				// for each clause, reset the label for the unlab block
				for (Clause c : (Vector<Clause>) le.clauses) {
					super.visit(c);
					curLabel = oldLabel;
				}
			}
		};

		Map<String, Set<PGoVariable>> varGroups = walker.getResult(data.ast);
		for (Entry<String, Set<PGoVariable>> e : varGroups.entrySet()) {
			// put all variables in this label into the same group
			Set<PGoVariable> toMerge = e.getValue();
			if (toMerge.isEmpty()) {
				continue;
			}
			PGoVariable first = toMerge.iterator().next();
			for (PGoVariable var : toMerge) {
				dsu.union(first, var);
			}
		}

		// map the representative PGoVariable of the set to the id number of the
		// lock group
		int id = 0;
		Map<PGoVariable, Integer> setToId = new HashMap<>();
		for (PGoVariable v : data.globals.values()) {
			PGoVariable rep = dsu.find(v);
			// if the variable is never accessed, doesn't need lock
			if (rep.getIsAtomic() && !setToId.containsKey(rep)) {
				setToId.put(rep, id);
				id++;
				data.numLockGroups++;
			}
		}

		// apply the ids to the variables
		for (PGoVariable var : data.globals.values()) {
			if (!var.getIsAtomic()) {
				continue;
			}
			PGoVariable varRoot = dsu.find(var);
			var.setLockGroup(setToId.get(varRoot));
		}

		// fill the labToLockGroup map
		for (Entry<String, Set<PGoVariable>> e : varGroups.entrySet()) {
			if (e.getValue().isEmpty()) {
				data.labToLockGroup.put(e.getKey(), -1);
				continue;
			}
			// find the group one of the variables is in
			PGoVariable first = e.getValue().iterator().next();
			first = dsu.find(first);
			if (!first.getIsAtomic()) {
				data.labToLockGroup.put(e.getKey(), -1);
				continue;
			}
			int labId = setToId.get(first);
			data.labToLockGroup.put(e.getKey(), labId);
		}
		if (data.numLockGroups > 0) {
			data.needsLock = true;
		}
	}

	// A basic disjoint-set union data structure
	private class DisjointSets {
		// maps the variable to the representative of the set
		Map<PGoVariable, PGoVariable> representative;

		DisjointSets() {
			representative = new HashMap<>();
			for (PGoVariable v : data.globals.values()) {
				representative.put(v, v);
			}
		}

		// Finds the representative of the set that var is in.
		PGoVariable find(PGoVariable var) {
			// we can use == since no copies of the vars are made
			if (representative.get(var) == var) {
				return var;
			}
			PGoVariable ret = find(representative.get(var));
			representative.put(var, ret);
			return ret;
		}

		// Merge the two sets given by a and b.
		void union(PGoVariable a, PGoVariable b) {
			PGoVariable aRoot = find(a), bRoot = find(b);
			representative.put(aRoot, bRoot);
		}
	}
}
