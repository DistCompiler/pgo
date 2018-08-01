package pgo.parser;

import pgo.InternalCompilerError;
import pgo.util.SourceLocation;

import java.util.*;

public class ParsingContext {

	public static class State {
		private LexicalContext.Mark mark;
		private NoCopyQueue<ParseAction> queue;

		public State(LexicalContext.Mark mark, NoCopyQueue<ParseAction> queue) {
			this.mark = mark;
			this.queue = queue;
		}

		public LexicalContext.Mark getMark() { return mark; }
		public NoCopyQueue<ParseAction> getQueue() { return queue; }
	}

	public final static class NoCopyQueue<T> {
		private List<T> objects;
		private int index;
		private Iterator<T> iterator;
		private NoCopyQueue<T> next;

		private NoCopyQueue(List<T> objects, int index, Iterator<T> iterator, NoCopyQueue<T> next) {
			this.objects = objects;
			this.index = index;
			this.iterator = iterator;
			this.next = next;
		}

		public NoCopyQueue(){
			this.objects = Collections.emptyList();
			this.index = 0;
			this.iterator = null;
			this.next = null;
		}

		public NoCopyQueue(List<T> elements){
			this.objects = elements;
			this.index = 0;
			this.iterator = null;
			this.next = null;
		}

		@Override
		public String toString() {
			return objects.subList(index, objects.size()).toString() + "; " + next;
		}

		public NoCopyQueue<T> duplicate() {
			return new NoCopyQueue<>(objects, index, null, next);
		}

		public void prepend(List<T> elements) {
			next = duplicate();
			objects = elements;
			index = 0;
			iterator = null;
		}

		public Optional<T> dequeue(){
			while(true){
				if (iterator == null && index < objects.size()) {
					iterator = objects.listIterator(index);
				}
				if (iterator != null && iterator.hasNext()) {
					++index;
					return Optional.of(iterator.next());
				}
				if (next != null) {
					objects = next.objects;
					index = next.index;
					next = next.next;
					iterator = null;
				}else{
					return Optional.empty();
				}
			}
		}
	}

	private LexicalContext lexicalContext;
	private NavigableMap<SourceLocation, Set<ParseFailure>> failures;
	private Deque<State> stateStack;
	private NoCopyQueue<ParseAction> queue;

	public ParsingContext(LexicalContext lexicalContext){
		this.lexicalContext = lexicalContext;
		this.failures = new TreeMap<>();
		this.stateStack = new ArrayDeque<>();
		this.queue = new NoCopyQueue<>();
	}

	public void addFailure(ParseFailure failure){
		SourceLocation loc = lexicalContext.getSourceLocation();
		if(!failures.containsKey(loc)){
			Set<ParseFailure> set = new HashSet<>();
			set.add(failure);
			failures.put(loc, set);
		}else{
			failures.get(loc).add(failure);
		}
	}

	public NavigableMap<SourceLocation, Set<ParseFailure>> getFailures() { return failures; }

	private void scheduleBranch(List<ParseAction> branch) {
		NoCopyQueue<ParseAction> copy = queue.duplicate();
		copy.prepend(branch);
		stateStack.push(new State(lexicalContext.mark(), copy));
	}

	private boolean speculateBranch(List<ParseAction> branch, List<ParseAction> suffix, ParseActionExecutor exec){
		int pos = 0;
		for(ParseAction action : branch) {
			if(action instanceof BranchParseAction) {
				List<List<ParseAction>> branches = ((BranchParseAction)action).getBranches();
				boolean result = false;
				List<ParseAction> nestedSuffix;
				if(suffix.isEmpty()) {
					nestedSuffix = branch.subList(pos+1, branch.size());
				}else{
					nestedSuffix = new ArrayList<>();
					nestedSuffix.addAll(branch.subList(pos+1, branch.size()));
					nestedSuffix.addAll(suffix);
				}
				for(int i = branches.size() - 1; i >= 0; --i){
					List<ParseAction> nestedBranch = branches.get(i);
					LexicalContext.Mark mark = lexicalContext.mark();
					result |= speculateBranch(nestedBranch, nestedSuffix, exec);
					lexicalContext.restore(mark);
				}
				return result;
			} else if(!action.isDecidable()) {
				List<ParseAction> full = new ArrayList<>();
				full.addAll(branch.subList(pos, branch.size()));
				full.addAll(suffix);
				//System.out.println("defer "+full);
				scheduleBranch(full);
				return true;
			} else if(!action.accept(exec)){
				List<ParseAction> full = new ArrayList<>();
				full.addAll(branch.subList(pos, branch.size()));
				full.addAll(suffix);
				//System.out.println("discard "+full);
				return false;
			}
			//System.out.println("success "+action);
			++pos;
		}
		if(suffix.isEmpty()){
			scheduleBranch(Collections.emptyList());
			return true;
		}else {
			return speculateBranch(suffix, Collections.emptyList(), exec);
		}
	}

	public boolean branch(List<List<ParseAction>> branches, ParseActionExecutor exec) {
		if(branches.size() == 0){
			return false;
		}

		boolean success = false;
		LexicalContext.Mark mark = lexicalContext.mark();

		for(int i = branches.size()-1; i >= 0; --i){
			List<ParseAction> branch = branches.get(i);
			// optimisation: is we can immediately try a parse action with no side-effects, try it in case it fails
			// if it fails we can drop the entire branch, saving a lot of work
			/*if(!branch.isEmpty() && branch.get(0).isDecidable()) {
				if(!branch.get(0).accept(exec)){
					continue;
				}
				thisMark = lexicalContext.mark();
				lexicalContext.restore(mark);
				branch = branch.subList(1, branch.size());
			}*/
			success |= speculateBranch(branch, Collections.emptyList(), exec);
			lexicalContext.restore(mark);
			/*NoCopyQueue<ParseAction> copy = queue.duplicate();
			copy.prepend(branch);
			stateStack.push(new State(mark, copy));*/
		}

		if(success) {
			State state = stateStack.pop();
			queue = state.getQueue();
			lexicalContext.restore(state.getMark());
			return true;
		}else{
			lexicalContext.restore(mark);
			return false;
		}
	}

	public boolean backtrack(){
		if(stateStack.isEmpty()){
			return false;
		}
		State state = stateStack.pop();
		queue = state.getQueue();
		lexicalContext.restore(state.getMark());
		//System.out.println("backtrack "+queue);
		return true;
	}

	public void preQueueActions(List<ParseAction> actions) {
		queue.prepend(actions);
	}

	public Optional<ParseAction> dequeueAction(){
		Optional<ParseAction> action = queue.dequeue();
		return action;
		//return queue.dequeue();
	}

}
