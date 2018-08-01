package pgo.parser;

import java.util.*;

public class ActionTrie {

	private List<ParseAction> prefix;
	private List<ActionTrie> successors;

	public ActionTrie(List<ParseAction> actions) {
		this.prefix = actions;
		this.successors = new ArrayList<>();
	}

	private ActionTrie(List<ParseAction> prefix, List<ActionTrie> successors) {
		this.prefix = prefix;
		this.successors = successors;
	}

	public void addActionSequence(List<ParseAction> newActions) {
		ListIterator<ParseAction> newIt = newActions.listIterator();
		ListIterator<ParseAction> existingIt = prefix.listIterator();
		boolean divergence = false;
		ParseAction newAction, existingAction;
		while(newIt.hasNext() && existingIt.hasNext()) {
			newAction = newIt.next();
			existingAction = existingIt.next();
			if(existingAction.mergeCompatible(newAction)){
				existingAction.merge(newAction);
			}else {
				divergence = true;
				break;
			}
		}
		if(divergence /* scenario 1 */ || existingIt.hasNext() /* scenario 2 */) {
			// scenario 1: if we diverged, split the current prefix between what matched and what didn't
			// (generates a new successor trie with the part of the prefix that did not match, and all the existing
			// successors to the entire prefix)

			List<ActionTrie> existingSucc = successors;
			List<ParseAction> existingActions = prefix;
			successors = new ArrayList<>();
			successors.add(new ActionTrie(
					existingActions.subList(existingIt.previousIndex(), existingActions.size()),
					existingSucc));
			prefix = existingActions.subList(0, existingIt.previousIndex());

			// scenario 2: we did not diverge but the new sequence is shorter than the prefix. we still have
			// to split the current prefix in the same way as above, but we also add an empty successor in order
			// to properly match only the new (sorter) sequence as well as the entire original prefix
			successors.add(new ActionTrie(Collections.emptyList()));
		}
		if(newIt.hasNext()) {
			// if we diverged from the prefix and have elements left in the new sequence, there is no point in trying
			// to merge with a successor since the last successor is the prefix we didn't match
			if(successors.isEmpty() || divergence) {
				successors.add(new ActionTrie(newActions.subList(newIt.previousIndex(), newActions.size())));
			}else {
				// if we didn't diverge but still have elements left in the new sequence, try to merge them
				// with the last successor
				List<ParseAction> remainingActions = newActions.subList(newIt.previousIndex(), newActions.size());
				successors.get(successors.size()-1).addActionSequence(remainingActions);
			}
		}
	}

	public List<ParseAction> getPrefix() { return prefix; }
	public List<ActionTrie> getSuccessors() { return successors; }

}
