package pgo.parser;

import pgo.util.EmptyHeterogenousList;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

import java.util.*;
import java.util.regex.MatchResult;

public class GrammarExecuteVisitor extends GrammarVisitor<GrammarExecuteVisitor.ParsingResult, RuntimeException> {

	static final class ParsingResultPair {
		private final LexicalContext.Mark mark;
		private final SourceLocatable result;

		ParsingResultPair(LexicalContext.Mark mark, SourceLocatable result) {
			this.mark = mark;
			this.result = result;
		}

		public LexicalContext.Mark getMark() {
			return mark;
		}

		public SourceLocatable getResult() {
			return result;
		}
	}

	static final class ParsingResult {
		private final List<ParsingResultPair> results;

		ParsingResult(List<ParsingResultPair> results) {
			this.results = results;
		}

		public List<ParsingResultPair> getResults() {
			return results;
		}
	}

	static final class MemoizeKey<Result extends SourceLocatable> {
		private final Grammar<Result> grammar;
		private final FrozenVariableMap variableMap;

		MemoizeKey(Grammar<Result> grammar, FrozenVariableMap variableMap) {
			this.grammar = grammar;
			this.variableMap = variableMap;
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			MemoizeKey that = (MemoizeKey) o;
			return Objects.equals(grammar, that.grammar) &&
					Objects.equals(variableMap, that.variableMap);
		}

		@Override
		public int hashCode() {
			return Objects.hash(grammar, variableMap);
		}
	}

	static final class MemoizeRecord {
		private final ParsingResult result;
		private final LexicalContext.Mark mark;

		MemoizeRecord(ParsingResult result, LexicalContext.Mark mark) {
			this.result = result;
			this.mark = mark;
		}

		public ParsingResult getResult() {
			return result;
		}

		public LexicalContext.Mark getMark() {
			return mark;
		}
	}

	static final class MemoizeTable {
		private final NavigableMap<SourceLocation, Integer> minLocations;
		private final NavigableMap<SourceLocation, Map<MemoizeKey, MemoizeRecord>> table;

		MemoizeTable() {
			this.minLocations = new TreeMap<>();
			this.table = new TreeMap<>();
		}

		void setMinLocation(SourceLocation loc) {
			Integer old = minLocations.putIfAbsent(loc, 1);
			if(old != null) {
				minLocations.put(loc, old+1);
			}
		}

		public void gc() {
			if(minLocations.isEmpty()) {
				table.clear();
			}else {
				table.headMap(minLocations.firstKey()).clear();
			}
		}

		void clearMinLocation(SourceLocation loc) {
			Integer val = minLocations.get(loc);
			if(val == 1) {
				minLocations.remove(loc);
				gc();
			}else{
				minLocations.put(loc, val-1);
			}
		}

		public MemoizeRecord get(SourceLocation location, MemoizeKey k) {
			Map<MemoizeKey, MemoizeRecord> nested = table.get(location);
			if(nested == null) return null;
			return nested.get(k);
		}

		public void put(SourceLocation loc, MemoizeKey k, MemoizeRecord rec) {
			Map<MemoizeKey, MemoizeRecord> nested = table.computeIfAbsent(loc, k1 -> new HashMap<>());
			nested.put(k, rec);
		}
	}

	private final MemoizeTable memoizeTable;
	private final FrozenVariableMap variableMap;
	private final LexicalContext lexicalContext;
	private final NavigableMap<SourceLocation, Set<ParseFailure>> failures;

	GrammarExecuteVisitor(LexicalContext lexicalContext, FrozenVariableMap variableMap,
						  NavigableMap<SourceLocation, Set<ParseFailure>> failures, MemoizeTable memoizeTable) {
		this.lexicalContext = lexicalContext;
		this.variableMap = variableMap;
		this.memoizeTable = memoizeTable;
		this.failures = failures;
	}

	private void addFailure(ParseFailure failure){
		SourceLocation loc = lexicalContext.getSourceLocation();
		if(!failures.containsKey(loc)){
			Set<ParseFailure> set = new HashSet<>();
			set.add(failure);
			failures.put(loc, set);
		}else{
			failures.get(loc).add(failure);
		}
	}

	private ParsingResult tryMemoize(Grammar<? extends SourceLocatable> grammar) {
		SourceLocation loc = lexicalContext.getSourceLocation();
		MemoizeKey key = new MemoizeKey(grammar, variableMap);
		MemoizeRecord record;
		if((record = memoizeTable.get(loc, key)) != null) {
			lexicalContext.restore(record.getMark());
			return record.getResult();
		}else{
			ParsingResult result = grammar.accept(this);
			memoizeTable.put(loc, key, new MemoizeRecord(result, lexicalContext.mark()));
			return result;
		}
	}

	public NavigableMap<SourceLocation, Set<ParseFailure>> getFailures() {
		return failures;
	}

	@Override
	public ParsingResult visit(PatternGrammar patternGrammar) throws RuntimeException {
		Optional<Located<MatchResult>> result = lexicalContext.matchPattern(patternGrammar.getPattern());
		if(result.isPresent()) {
			return new ParsingResult(Collections.singletonList(
					new ParsingResultPair(lexicalContext.mark(), result.get())));
		}else{
			addFailure(ParseFailure.patternMatchFailure(lexicalContext.getSourceLocation(), patternGrammar.getPattern()));
			return new ParsingResult(Collections.emptyList());
		}
	}

	@Override
	@SuppressWarnings("unchecked")
	public <
			GrammarPredecessorResult extends SourceLocatable,
			GrammarResult extends SourceLocatable
			> ParsingResult visit(MappingGrammar<GrammarPredecessorResult, GrammarResult> mappingGrammar) throws RuntimeException {
		ParsingResult predecessorResult = mappingGrammar.getPredecessorGrammar().accept(this);
		if(predecessorResult.getResults().isEmpty()) {
			return predecessorResult;
		}else if(predecessorResult.getResults().size() == 1) {
			ParsingResultPair theResult = predecessorResult.getResults().get(0);
			GrammarResult mappedResult = mappingGrammar
					.getMapping()
					.apply((GrammarPredecessorResult)theResult.getResult());
			return new ParsingResult(
					Collections.singletonList(
							new ParsingResultPair(
									theResult.getMark(),
									mappedResult)));
		}else{
			List<ParsingResultPair> mapped = new ArrayList<>();
			for(ParsingResultPair prev : predecessorResult.getResults()) {
				mapped.add(new ParsingResultPair(
						prev.getMark(),
						mappingGrammar.getMapping().apply((GrammarPredecessorResult)prev.getResult())));
			}
			return new ParsingResult(mapped);
		}
	}

	@Override
	public <GrammarResult extends SourceLocatable> ParsingResult visit(ReferenceGrammar<GrammarResult> referenceGrammar) throws RuntimeException {
		return referenceGrammar.getReferencedGrammar().accept(this);
	}

	@Override
	public ParsingResult visit(StringGrammar stringGrammar) throws RuntimeException {
		Optional<Located<Void>> result = lexicalContext.matchString(stringGrammar.getString());
		if(result.isPresent()) {
			return new ParsingResult(Collections.singletonList(
					new ParsingResultPair(lexicalContext.mark(), result.get())));
		}else{
			addFailure(ParseFailure.stringMatchFailure(lexicalContext.getSourceLocation(), stringGrammar.getString()));
			return new ParsingResult(Collections.emptyList());
		}
	}

	@Override
	public <GrammarResult extends SourceLocatable> ParsingResult visit(BranchGrammar<GrammarResult> branchGrammar) throws RuntimeException {
		List<? extends Grammar<? extends GrammarResult>> branches = branchGrammar.getBranches();
		List<ParsingResultPair> results = new ArrayList<>();
		SourceLocation possibleMinLocation = lexicalContext.getSourceLocation();
		memoizeTable.setMinLocation(possibleMinLocation);
		LexicalContext.Mark mark = lexicalContext.mark();
		for(Grammar<? extends GrammarResult> branch : branches) {
			lexicalContext.restore(mark);
			results.addAll(branch.accept(this).getResults());
		}
		memoizeTable.clearMinLocation(possibleMinLocation);
		return new ParsingResult(results);
	}

	@Override
	public ParsingResult visit(EmptySequenceGrammar emptySequenceGrammar) throws RuntimeException {
		return new ParsingResult(Collections.singletonList(new ParsingResultPair(
				lexicalContext.mark(), new Located<>(SourceLocation.unknown(), new EmptyHeterogenousList()))));
	}

	@Override
	public <Dropped extends SourceLocatable, Rest extends EmptyHeterogenousList> ParsingResult visit(DropSequenceGrammar<Dropped, Rest> dropSequenceGrammar) {
		ParsingResult restResult = dropSequenceGrammar.getPrevious().accept(this);
		List<ParsingResultPair> results = new ArrayList<>();
		for(ParsingResultPair prevResult : restResult.getResults()) {
			lexicalContext.restore(prevResult.getMark());
			ParsingResult currentResult = dropSequenceGrammar.getDropped().accept(this);
			for(ParsingResultPair p : currentResult.getResults()) {
				Located<?> nResult = (Located<?>)prevResult.getResult();
				results.add(new ParsingResultPair(
						p.getMark(),
						new Located<>(
								p.getResult().getLocation().combine(nResult.getLocation()),
								nResult.getValue())));
			}
		}
		return new ParsingResult(results);
	}

	@Override
	@SuppressWarnings("unchecked")
	public <Part extends SourceLocatable, Rest extends EmptyHeterogenousList> ParsingResult visit(PartSequenceGrammar<Part, Rest> partSequenceGrammar) {
		ParsingResult restResult = partSequenceGrammar.getPrevGrammar().accept(this);
		List<ParsingResultPair> results = new ArrayList<>();
		for(ParsingResultPair prevResult : restResult.getResults()) {
			lexicalContext.restore(prevResult.getMark());
			ParsingResult currentResult = partSequenceGrammar.getCurrent().accept(this);
			for(ParsingResultPair p : currentResult.getResults()) {
				Located<Rest> prev = (Located<Rest>)prevResult.getResult();
				results.add(new ParsingResultPair(
						p.getMark(),
						new Located<>(
								p.getResult().getLocation().combine(prev.getLocation()),
								prev.getValue().cons(p.getResult()))
				));
			}
		}
		return new ParsingResult(results);
	}

	@Override
	@SuppressWarnings("unchecked")
	public <GrammarResult extends SourceLocatable, PredecessorResult extends EmptyHeterogenousList> ParsingResult visit(CallGrammar<GrammarResult, PredecessorResult> callGrammar) {
		ParsingResult precedessorResult = callGrammar.getPredecessor().accept(this);
		List<ParsingResultPair> results = new ArrayList<>();
		for(ParsingResultPair prevResult : precedessorResult.getResults()) {
			lexicalContext.restore(prevResult.getMark());
			ParsingResult currentResult = callGrammar.getTarget().accept(new GrammarExecuteVisitor(
					lexicalContext,
					callGrammar
							.getMappingGenerator()
							.apply(new ParseInfo<>(
									(Located<PredecessorResult>) prevResult.getResult(),
									variableMap))
							.freeze(),
					failures,
					memoizeTable));
			for(ParsingResultPair p : currentResult.getResults()) {
				Located<PredecessorResult> prev = (Located<PredecessorResult>)prevResult.getResult();
				results.add(new ParsingResultPair(
						p.getMark(),
						new Located<>(
								prev.getLocation().combine(p.getResult().getLocation()),
								prev.getValue().cons(p.getResult()))
				));
			}
		}
		return new ParsingResult(results);
	}

	@Override
	public <GrammarResult extends SourceLocatable> ParsingResult visit(CutGrammar<GrammarResult> cutGrammar) throws RuntimeException {
		ParsingResult result = cutGrammar.getToCut().accept(this);
		if(result.getResults().isEmpty()) {
			return result;
		}else{
			return new ParsingResult(Collections.singletonList(result.getResults().get(0)));
		}
	}

	@Override
	public <GrammarResult extends SourceLocatable> ParsingResult visit(MemoizeGrammar<GrammarResult> memoizeGrammar) throws RuntimeException {
		return tryMemoize(memoizeGrammar.getToMemoize());
	}

	@Override
	@SuppressWarnings("unchecked")
	public <GrammarResult extends SourceLocatable> ParsingResult visit(PredicateGrammar<GrammarResult> predicateGrammar) throws RuntimeException {
		ParsingResult prevResult = predicateGrammar.getToFilter().accept(this);
		List<ParsingResultPair> results = new ArrayList<>(prevResult.getResults().size());
		for(ParsingResultPair p : prevResult.getResults()) {
			if(predicateGrammar.getPredicate().test(new ParseInfo<>((GrammarResult)p.getResult(), variableMap))) {
				results.add(p);
			}
		}
		return new ParsingResult(results);
	}

	@Override
	public <GrammarResult extends SourceLocatable> ParsingResult visit(RejectGrammar<GrammarResult> rejectGrammar) throws RuntimeException {
		Grammar<GrammarResult> toReject = rejectGrammar.getToReject();
		LexicalContext.Mark mark = lexicalContext.mark();
		ParsingResult result = toReject.accept(new GrammarExecuteVisitor(lexicalContext, variableMap, new TreeMap<>(), memoizeTable));
		if(result.getResults().isEmpty()) {
			return new ParsingResult(Collections.singletonList(
					new ParsingResultPair(mark, new Located<Void>(lexicalContext.getSourceLocation(), null))));
		}else{
			// if the grammar succceeds in any way, fail
			addFailure(ParseFailure.rejectFailure(toReject));
			return new ParsingResult(Collections.emptyList());
		}
	}

	@Override
	public ParsingResult visit(EOFGrammar eofGrammar) throws RuntimeException {
		if(lexicalContext.isEOF()) {
			return new ParsingResult(Collections.singletonList(
					new ParsingResultPair(
							lexicalContext.mark(),
							new Located<>(lexicalContext.getSourceLocation(), null))));
		}else{
			addFailure(ParseFailure.eofMatchFailure());
			return new ParsingResult(Collections.emptyList());
		}
	}
}
