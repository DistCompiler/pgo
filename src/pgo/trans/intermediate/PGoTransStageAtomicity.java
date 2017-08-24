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
 * TODO we can probably optimize this in terms of locking. Also need to deal
 * with networks
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
			protected void visit(SingleAssign sa) {
				// we only care about global variables, so don't use
				// findPGoVariable
				PGoVariable toInsert = data.globals.get(sa.lhs.var);
				if (toInsert != null) {
					result.get(curLabel).add(toInsert);
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
		for (PGoVariable v : dsu.representative.values()) {
			if (!setToId.containsKey(v)) {
				setToId.put(v, id);
				id++;
				data.numLockGroups++;
			}
		}

		// apply the ids to the variables
		for (PGoVariable var : data.globals.values()) {
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
			int labId = setToId.get(first);
			data.labToLockGroup.put(e.getKey(), labId);
		}
		data.needsLock = true;
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
			if (aRoot != bRoot) {
				representative.put(aRoot, bRoot);
			}
		}
	}
}
