package pgo.parser;

import pgo.InternalCompilerError;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

import java.util.*;
import java.util.regex.MatchResult;
import java.util.regex.Pattern;

public class ParsingContext implements ParseActionExecutor {

	public static class State {
		private LexicalContext.Mark mark;
		private NoCopyQueue<ParseAction> queue;
		private NoCopyStack<SourceLocatable[]> storeStack;
		private NoCopyStack<SourceLocatable[]> variableStoreStack;
		private NoCopyStack<Map<Variable, Integer>> variableMapStack;
		private NoCopyStack<Integer> returnDestStack;

		public State(LexicalContext.Mark mark, NoCopyQueue<ParseAction> queue, NoCopyStack<SourceLocatable[]> storeStack,
					 NoCopyStack<SourceLocatable[]> variableStoreStack, NoCopyStack<Map<Variable, Integer>> variableMapStack,
					 NoCopyStack<Integer> returnDestStack) {
			this.mark = mark;
			this.queue = queue;
			this.storeStack = storeStack;
			this.variableStoreStack = variableStoreStack;
			this.variableMapStack = variableMapStack;
			this.returnDestStack = returnDestStack;
		}

		public State duplicate() {
			return new State(mark, queue.duplicate(), storeStack.duplicate(), variableStoreStack.duplicate(),
					variableMapStack.duplicate(), returnDestStack.duplicate());
		}

		public LexicalContext.Mark getMark() { return mark; }
		public NoCopyQueue<ParseAction> getQueue() { return queue; }
		public NoCopyStack<SourceLocatable[]> getStoreStack() { return storeStack; }
		public NoCopyStack<SourceLocatable[]> getVariableStoreStack() { return variableStoreStack; }
		public NoCopyStack<Map<Variable, Integer>> getVariableMapStack() { return variableMapStack; }
		public NoCopyStack<Integer> getReturnDestStack() { return returnDestStack; }

		public SourceLocatable getStoreObject(int offset) {
			return storeStack.top()[offset];
		}
		public void setStoreObject(int offset, SourceLocatable object) {
			storeStack.top()[offset] = object;
		}

		public void setVariable(int offset, SourceLocatable object) {
			variableStoreStack.top()[offset] = object;
		}
		public void setVariable(Variable name, SourceLocatable object) {
			setVariable(variableMapStack.top().get(name), object);
		}
		public SourceLocatable getVariable(int offset) {
			return variableStoreStack.top()[offset];
		}

		public void setMark(LexicalContext.Mark mark) { this.mark = mark; }
	}

	private LexicalContext lexicalContext;
	private NavigableMap<SourceLocation, Set<ParseFailure>> failures;
	private NoCopyStack<State> stateStack;
	private State currentState;

	public ParsingContext(LexicalContext lexicalContext, CompiledGrammar compiledGrammar){
		this.lexicalContext = lexicalContext;
		this.failures = new TreeMap<>();
		this.stateStack = new NoCopyStack<>();
		this.currentState = new State(
				lexicalContext.mark(),
				new NoCopyQueue<>(),
				new NoCopyStack<>(new SourceLocatable[compiledGrammar.getStoreSize()]),
				new NoCopyStack<>(new SourceLocatable[compiledGrammar.getVariableLocations().size()]),
				new NoCopyStack<>(compiledGrammar.getVariableLocations()),
				new NoCopyStack<>());
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
		State dupState = currentState.duplicate();
		dupState.getQueue().prepend(branch);
		dupState.setMark(lexicalContext.mark());
		stateStack.push(dupState);
	}

	private boolean speculateBranch(List<ParseAction> branch, List<ParseAction> suffix){
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
					result |= speculateBranch(nestedBranch, nestedSuffix);
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
			} else if(!action.accept(this)){
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
			return speculateBranch(suffix, Collections.emptyList());
		}
	}

	public boolean backtrack(){
		if(stateStack.isEmpty()){
			return false;
		}
		currentState = stateStack.pop().get();
		lexicalContext.restore(currentState.getMark());
		return true;
	}

	public void preQueueActions(List<ParseAction> actions) {
		currentState.getQueue().prepend(actions);
	}

	public Optional<ParseAction> dequeueAction(){
		Optional<ParseAction> action = currentState.getQueue().dequeue();
		return action;
	}

	public <Type extends SourceLocatable> Type getVariableValue(Variable<Type> v) {
		Map<Variable, Integer> varMap = currentState.getVariableMapStack().top();
		SourceLocatable[] varStore = currentState.getVariableStoreStack().top();
		if(varMap.containsKey(v)) {
			Type value = (Type)varStore[varMap.get(v)];
			//System.out.println("read var "+v+" = "+value);
			if(value != null) {
				return value;
			}
		}
		if(currentState.getVariableMapStack().hasNext()) {
			currentState.getVariableMapStack().pop();
			currentState.getVariableStoreStack().pop();
			Type result = getVariableValue(v);
			currentState.getVariableMapStack().push(varMap);
			currentState.getVariableStoreStack().push(varStore);
			return result;
		}
		throw new InternalCompilerError();
	}

	@Override
	public boolean visit(StringParseAction stringParseAction) {
		String token = stringParseAction.getToMatch();
		Optional<Located<Void>> loc = lexicalContext.matchString(token);
		if(loc.isPresent()){
			if(stringParseAction.getToMatch().length() != 0 && !Arrays.asList("\\*", "(*", "*)").contains(stringParseAction.getToMatch())) {
				System.out.println("match string \"" + token + "\" " + loc.get().getLocation());
			}
			currentState.setStoreObject(stringParseAction.getResultLocation(), loc.get());
			return true;
		}else{
			//System.out.println("fail string \""+token+"\" "+lexicalContext.getSourceLocation());
			addFailure(ParseFailure.stringMatchFailure(lexicalContext.getSourceLocation(), token));
			return false;
		}
	}

	@Override
	public boolean visit(PatternParseAction patternParseAction) {
		Pattern pattern = patternParseAction.getToMatch();
		Optional<Located<MatchResult>> res = lexicalContext.matchPattern(pattern);
		if(res.isPresent()){
			String s = res.get().getValue().group();
			if(!s.startsWith(" ") && !s.startsWith("\n")){
				System.out.println("match pat "+s+" "+res.get().getLocation());
			}
			//System.out.println("match pattern \""+pattern+"\" "+res.get().getLocation());
			currentState.setStoreObject(patternParseAction.getResultLocation(), res.get());
			return true;
		}else{
			//System.out.println("fail pattern \""+pattern+"\" "+lexicalContext.getSourceLocation());
			addFailure(ParseFailure.patternMatchFailure(lexicalContext.getSourceLocation(), pattern));
			return false;
		}
	}

	@Override
	public boolean visit(FailParseAction failParseAction) {
		for(ParseFailure failure : failParseAction.getFailures()){
			addFailure(failure);
		}
		return false;
	}

	@Override
	public boolean visit(BranchParseAction branchParseAction) {
		List<List<ParseAction>> branches = branchParseAction.getBranches();
		if(branches.size() == 0){
			return false;
		}

		boolean success = false;
		LexicalContext.Mark mark = lexicalContext.mark();

		for(int i = branches.size()-1; i >= 0; --i){
			List<ParseAction> branch = branches.get(i);
			success |= speculateBranch(branch, Collections.emptyList());
			lexicalContext.restore(mark);
		}

		// if any branch resulted in a deferral, backtrack so that it will be the next one selected
		if(success) {
			return backtrack();
		}else{
			return false;
		}
	}

	@Override
	public boolean visit(MappingParseAction mappingParseAction) {
		SourceLocatable before = currentState.getStoreObject(mappingParseAction.getLocation());
		//System.out.print("mapping "+mappingParseAction.getLocation() + "; "+before+" -> ");
		currentState.setStoreObject(
				mappingParseAction.getLocation(),
				(SourceLocatable)mappingParseAction.getMapping().apply(
						currentState.getStoreObject(mappingParseAction.getLocation())));
		//System.out.println(currentState.getStoreObject(mappingParseAction.getLocation()));
		return true;
	}

	@Override
	public boolean visit(ReturnParseAction returnParseAction) {
		// only if we're not at the bottom of the callstack already - makes it safe to add returns to all sequences
		if(currentState.getStoreStack().hasNext()) {
			SourceLocatable value = currentState.getStoreObject(returnParseAction.getReturnSource());
			currentState.getStoreStack().pop();
			currentState.getVariableMapStack().pop();
			currentState.getVariableStoreStack().pop();

			int returnDest = currentState.getReturnDestStack().pop().get();

			//System.out.println("return "+returnParseAction.getReturnSource()+" -("+value+")-> "+returnDest);

			currentState.setStoreObject(returnDest, value);
		}
		return true;
	}

	@Override
	public boolean visit(ReferenceParseAction referenceParseAction) {
		Map<Variable, Variable> substitutions = referenceParseAction.getSubstitutions();

		// pull values of variables we want to propagate
		List<SourceLocatable> values = new ArrayList<>(substitutions.size());
		List<Variable> locations = new ArrayList<>(substitutions.size());
		for(Map.Entry<Variable, Variable> sub : substitutions.entrySet()) {
			values.add(getVariableValue(sub.getKey()));
			locations.add(sub.getValue());
		}

		// push callstack
		CompiledGrammar grammar = referenceParseAction.getReferencedGrammar();
		currentState.getStoreStack().push(new SourceLocatable[grammar.getStoreSize()]);
		currentState.getVariableStoreStack().push(new SourceLocatable[grammar.getVariableLocations().size()]);
		currentState.getVariableMapStack().push(grammar.getVariableLocations());
		currentState.getQueue().prepend(grammar.getActions());
		currentState.getReturnDestStack().push(referenceParseAction.getReturnDest());

		//System.out.println("reference "+locations+" == "+values);

		// add any extra values we want to propagate
		Iterator<SourceLocatable> itVal = values.iterator();
		Iterator<Variable> itLoc = locations.iterator();
		while(itVal.hasNext()) {
			Variable loc = itLoc.next();
			SourceLocatable val = itVal.next();
			//System.out.println("propagating "+loc+" = "+val);
			currentState.setVariable(loc, val);
		}
		return true;
	}

	@Override
	public boolean visit(AssignmentParseAction assignmentParseAction) {
		/*System.out.println(
				"assign "+assignmentParseAction.getFromLocation()+" ("+currentState.getStoreObject(assignmentParseAction.getFromLocation())
						+") -> "+assignmentParseAction.getToLocation()+" ("+currentState.getStoreObject(assignmentParseAction.getToLocation())+")");*/
		currentState.setStoreObject(assignmentParseAction.getToLocation(),
				currentState.getStoreObject(assignmentParseAction.getFromLocation()));
		return true;
	}

	@Override
	public boolean visit(AccumulateLocationsParseAction accumulateLocationsParseAction) {
		SourceLocation loc = SourceLocation.unknown();
		for(Integer location : accumulateLocationsParseAction.getPartLocations()) {
			loc = loc.combine(currentState.getStoreObject(location).getLocation());
		}
		currentState.setStoreObject(accumulateLocationsParseAction.getDestinationLocation(),
				new ParseInfo<Located<Void>>(new Located<>(loc, null), this));
		return true;
	}

	@Override
	public boolean visit(StoreValueParseAction storeValueParseAction) {
		/*System.out.println("write var "+storeValueParseAction.getDestVariable()+" "
				+currentState.getStoreObject(storeValueParseAction.getDestination())+" -> "
				+currentState.getStoreObject(storeValueParseAction.getSource()));*/
		currentState.setVariable(
				storeValueParseAction.getDestination(),
				currentState.getStoreObject(storeValueParseAction.getSource()));
		return true;
	}

	@Override
	public boolean visit(PredicateParseAction predicateParseAction) {
		return predicateParseAction.getPredicate().test(
				new ParseInfo<>(currentState.getStoreObject(predicateParseAction.getArgLocation()), this));
	}

	@Override
	public boolean visit(RejectParseAction rejectParseAction) {
		NoCopyStack<State> storedStateStack = stateStack.duplicate();

		State storedState = currentState.duplicate();
		NavigableMap<SourceLocation, Set<ParseFailure>> storedFailures = failures;
		failures = new TreeMap<>();
		LexicalContext.Mark mark = lexicalContext.mark();
		stateStack = new NoCopyStack<>();

		boolean result = false;
		// try the sequence of actions until something fails or we run out
		currentState.getQueue().clear(); // only try these actions; not the already queued ones.
		preQueueActions(rejectParseAction.getToReject());
		Optional<ParseAction> currentAction = dequeueAction();
		while(currentAction.isPresent()) {
			if(!currentAction.get().accept(this)){
				if(!backtrack()) {
					result = true;
					break;
				}
			}
			currentAction = dequeueAction();
		}

		lexicalContext.restore(mark);
		currentState = storedState;
		failures = storedFailures;
		stateStack = storedStateStack;

		addFailure(ParseFailure.rejectFailure(rejectParseAction.getToReject()));

		return result;
	}

	@Override
	public boolean visit(EOFParseAction eofParseAction) {
		if(!lexicalContext.isEOF()) {
			addFailure(ParseFailure.eofMatchFailure());
			return false;
		}
		return true;
	}

	public SourceLocatable getResult() {
		SourceLocatable[] store = currentState.getStoreStack().top();
		return store[store.length-1];
	}

}
