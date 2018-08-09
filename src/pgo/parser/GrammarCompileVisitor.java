package pgo.parser;

import pgo.util.SourceLocatable;

import java.util.*;

public class GrammarCompileVisitor<Result extends SourceLocatable> extends GrammarVisitor<Void, RuntimeException> {

	private int storeSize;
	private List<ParseAction> actions;
	private Map<Variable, Integer> variableMap;

	public GrammarCompileVisitor() {
		storeSize = 0;
		actions = new ArrayList<>();
		variableMap = new HashMap<>();
	}

	public CompiledGrammar<Result> getCompiledGrammar() {
		actions.add(new ReturnParseAction(storeSize-1));
		return new CompiledGrammar<>(storeSize, actions, variableMap);
	}

	@Override
	public Void visit(PatternGrammar patternGrammar) throws RuntimeException {
		actions.add(new PatternParseAction(patternGrammar.getPattern(), storeSize));
		++storeSize;
		return null;
	}

	@Override
	public <GrammarPredecessorResult extends SourceLocatable, GrammarResult extends SourceLocatable> Void visit(MappingGrammar<GrammarPredecessorResult, GrammarResult> mappingGrammar) throws RuntimeException {
		mappingGrammar.getPredecessorGrammar().accept(this);
		actions.add(new MappingParseAction<>(storeSize-1, mappingGrammar.getMapping()));
		return null;
	}

	@Override
	public <GrammarResult extends SourceLocatable> Void visit(FixPointGrammar<GrammarResult> fixPointGrammar) throws RuntimeException {
		ReferenceGrammar<GrammarResult> ref = new ReferenceGrammar<>();
		Grammar<GrammarResult> fix = fixPointGrammar.getFixPoint().apply(ref);
		GrammarCompileVisitor<GrammarResult> nested = new GrammarCompileVisitor<>();
		fix.accept(nested);
		CompiledGrammar<GrammarResult> compiled = nested.getCompiledGrammar();
		ref.setReferencedGrammar(compiled);

		ref.accept(this);
		return null;
	}

	@Override
	public <GrammarResult extends SourceLocatable> Void visit(ReferenceGrammar<GrammarResult> referenceGrammar) throws RuntimeException {
		actions.add(new ReferenceParseAction(
				referenceGrammar.getReferencedGrammar(),
				referenceGrammar.getSubstitutions(),
				storeSize));
		++storeSize;
		return null;
	}

	@Override
	public Void visit(StringGrammar stringGrammar) throws RuntimeException {
		actions.add(new StringParseAction(stringGrammar.getString(), storeSize));
		++storeSize;
		return null;
	}

	@Override
	public <GrammarResult extends SourceLocatable> Void visit(BranchGrammar<GrammarResult> branchGrammar) throws RuntimeException {
		List<ParseAction> storedActions = actions;
		List<List<ParseAction>> branchActions = new ArrayList<>(branchGrammar.getBranches().size());
		List<Integer> branchResults = new ArrayList<>(branchGrammar.getBranches().size());
		for(Grammar<? extends GrammarResult> branch : branchGrammar.getBranches()) {
			actions = new ArrayList<>();
			// don't reset storeSize as it might be unsafe to have different branches sharing the same store locations
			branch.accept(this);
			branchResults.add(storeSize-1);
			branchActions.add(actions);
		}

		int combinedResultLocation = storeSize;
		++storeSize;

		Iterator<Integer> currentEndPos = branchResults.iterator();
		for(List<ParseAction> branch : branchActions) {
			branch.add(new AssignmentParseAction(currentEndPos.next(), combinedResultLocation));
		}

		actions = storedActions;
		actions.add(new BranchParseAction(branchActions));
		return null;
	}

	@Override
	public Void visit(SequenceGrammar sequenceGrammar) throws RuntimeException {
		List<Integer> partResultLocations = new ArrayList<>(sequenceGrammar.getParts().size());
		for(Grammar<Located<Void>> part : sequenceGrammar.getParts()) {
			part.accept(this);
			partResultLocations.add(storeSize-1);
		}
		// store the accumulated locations of all results in a new slot
		actions.add(new AccumulateLocationsParseAction(partResultLocations, storeSize));
		++storeSize;
		return null;
	}

	@Override
	public <GrammarResult extends SourceLocatable> Void visit(AssignmentGrammar<GrammarResult> assignmentGrammar) throws RuntimeException {
		assignmentGrammar.getGrammar().accept(this);
		variableMap.putIfAbsent(assignmentGrammar.getVariable(), variableMap.size());
		actions.add(new StoreValueParseAction(storeSize-1, variableMap.get(assignmentGrammar.getVariable()),
				assignmentGrammar.getVariable()));
		return null;
	}

	@Override
	public <GrammarResult extends SourceLocatable> Void visit(PredicateGrammar<GrammarResult> predicateGrammar) throws RuntimeException {
		predicateGrammar.getToFilter().accept(this);
		actions.add(new PredicateParseAction<>(storeSize-1, predicateGrammar.getPredicate()));
		return null;
	}

	@Override
	public <GrammarResult extends SourceLocatable> Void visit(RejectGrammar<GrammarResult> rejectGrammar) throws RuntimeException {
		List<ParseAction> storedActions = actions;
		actions = new ArrayList<>();
		rejectGrammar.getToReject().accept(this);
		List<ParseAction> rejectedActions = actions;
		actions = storedActions;

		actions.add(new RejectParseAction(rejectedActions));
		actions.add(new StringParseAction("", storeSize));
		++storeSize;
		return null;
	}

	@Override
	public Void visit(EOFGrammar eofGrammar) throws RuntimeException {
		actions.add(new EOFParseAction());
		return null;
	}

	@Override
	public <GrammarResult extends SourceLocatable> Void visit(ArgumentGrammar<GrammarResult> argumentGrammar) throws RuntimeException {
		variableMap.putIfAbsent(argumentGrammar.getVariable(), variableMap.size());
		argumentGrammar.getGrammar().accept(this);
		return null;
	}
}
