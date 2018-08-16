package pgo.parser;

import pgo.TODO;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.regex.MatchResult;

public class GrammarExecuteVisitor extends GrammarVisitor<GrammarExecuteVisitor.ParsingResult, RuntimeException> {

	static final class ParsingResult {
		private final SourceLocatable result;
		private final Supplier<ParsingResult> retry;

		public ParsingResult(SourceLocatable result, Supplier<ParsingResult> retry) {
			this.result = result;
			this.retry = retry;
		}

		public SourceLocatable getResult() {
			return result;
		}

		public Supplier<ParsingResult> getRetry() {
			return retry;
		}
	}

	static final class MemoizeKey {
		private final SourceLocation sourceLocation;
		private final Grammar grammar;
		private final FrozenVariableMap variableMap;

		public MemoizeKey(SourceLocation sourceLocation, Grammar grammar, FrozenVariableMap variableMap) {
			this.sourceLocation = sourceLocation;
			this.grammar = grammar;
			this.variableMap = variableMap;
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			MemoizeKey that = (MemoizeKey) o;
			return Objects.equals(sourceLocation, that.sourceLocation) &&
					Objects.equals(grammar, that.grammar) &&
					Objects.equals(variableMap, that.variableMap);
		}

		@Override
		public int hashCode() {
			return Objects.hash(sourceLocation, grammar, variableMap);
		}
	}

	static final class MemoizeRecord {
		private final ParsingResult result;
		private final LexicalContext.Mark mark;

		public MemoizeRecord(ParsingResult result, LexicalContext.Mark mark) {
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
		private final Deque<MemoizeKey> lru;
		private final Map<MemoizeKey, MemoizeRecord> table;
		private static final int MAX_SIZE = 1000000;

		public MemoizeTable() {
			this.lru = new ArrayDeque<>(MAX_SIZE);
			this.table = new HashMap<>(MAX_SIZE);
		}

		public MemoizeRecord get(MemoizeKey k) {
			return table.get(k);
		}

		public void put(MemoizeKey k, MemoizeRecord rec) {
			if(table.put(k, rec) == null) {
				if(table.size() >= MAX_SIZE) {
					//System.out.println("size "+table.size());
					table.remove(lru.removeFirst());
				}
				lru.addLast(k);
			}
		}
	}

	private final MemoizeTable memoizeTable;
	private final FrozenVariableMap variableMap;
	private final LexicalContext lexicalContext;
	private final NavigableMap<SourceLocation, Set<ParseFailure>> failures;

	public GrammarExecuteVisitor(LexicalContext lexicalContext, FrozenVariableMap variableMap, NavigableMap<SourceLocation, Set<ParseFailure>> failures, MemoizeTable memoizeTable) {
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
		if(grammar instanceof StringGrammar || grammar instanceof PatternGrammar) {
			return grammar.accept(this);
		}

		MemoizeKey key = new MemoizeKey(lexicalContext.getSourceLocation(), grammar, variableMap);
		MemoizeRecord record;
		if((record = memoizeTable.get(key)) != null) {
			lexicalContext.restore(record.getMark());
			return record.getResult();
		}else{
			ParsingResult result = grammar.accept(this);
			memoizeTable.put(key, new MemoizeRecord(result, lexicalContext.mark()));
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
			String s = result.get().getValue().group();
			/*if(!s.startsWith(" ") && !s.startsWith("\n")) {
				System.out.println("pat " + s + " at " + result.get().getLocation());
			}*/
			return new ParsingResult(result.get(), null);
		}else{
			/*if(patternGrammar.getPattern() != ParseTools.WHITESPACE) {
				System.out.println("pat fail " + patternGrammar.getPattern() + " at " + lexicalContext.getSourceLocation());
			}*/
			addFailure(ParseFailure.patternMatchFailure(lexicalContext.getSourceLocation(), patternGrammar.getPattern()));
			return new ParsingResult(null, null);
		}
	}

	private static final class MappingRetry implements Supplier<ParsingResult> {

		private final Function<SourceLocatable, SourceLocatable> mapping;
		private final Supplier<ParsingResult> nestedRetry;

		public MappingRetry(Function<SourceLocatable, SourceLocatable> mapping, Supplier<ParsingResult> nestedRetry) {
			this.mapping = mapping;
			this.nestedRetry = nestedRetry;
		}

		@Override
		public ParsingResult get() {
			ParsingResult nestedResult = nestedRetry.get();
			if(nestedResult.getResult() != null) {
				return new ParsingResult(
						mapping.apply(nestedResult.getResult()),
						nestedResult.getRetry() != null ?
								new MappingRetry(mapping, nestedResult.getRetry())
								: null);
			}
			assert nestedResult.getRetry() == null;
			return nestedResult;
		}
	}

	@Override
	public <
			GrammarPredecessorResult extends SourceLocatable,
			GrammarResult extends SourceLocatable
			> ParsingResult visit(MappingGrammar<GrammarPredecessorResult, GrammarResult> mappingGrammar) throws RuntimeException {
		ParsingResult predecessorResult = tryMemoize(mappingGrammar.getPredecessorGrammar());

		if(predecessorResult.getResult() != null) {
			return new ParsingResult(
					Objects.requireNonNull(
							mappingGrammar.getMapping().apply((GrammarPredecessorResult)predecessorResult.getResult())),
					predecessorResult.getRetry() != null ?
							new MappingRetry(
									(Function<SourceLocatable, SourceLocatable>)mappingGrammar.getMapping(),
									predecessorResult.getRetry())
							: null);
		}
		assert predecessorResult.getRetry() == null;
		return predecessorResult;
	}

	@Override
	public <GrammarResult extends SourceLocatable> ParsingResult visit(ReferenceGrammar<GrammarResult> referenceGrammar) throws RuntimeException {
		return tryMemoize(referenceGrammar.getReferencedGrammar());
	}

	@Override
	public ParsingResult visit(StringGrammar stringGrammar) throws RuntimeException {
		Optional<Located<Void>> result = lexicalContext.matchString(stringGrammar.getString());
		if(result.isPresent()) {
			/*if(stringGrammar.getString().length() != 0) {
				System.out.println("str " + stringGrammar.getString() + " at " + result.get().getLocation());
			}*/
			return new ParsingResult(result.get(), null);
		}else{
			/*if(!Arrays.asList("(*", "*)", "\\*").contains(stringGrammar.getString())) {
				System.out.println("fail str " + stringGrammar.getString() + " at " + lexicalContext.getSourceLocation());
			}*/
			addFailure(ParseFailure.stringMatchFailure(lexicalContext.getSourceLocation(), stringGrammar.getString()));
			return new ParsingResult(null, null);
		}
	}

	private static class ChainRetry implements Supplier<ParsingResult> {

		private final Supplier<ParsingResult> before;
		private final Supplier<ParsingResult> after;

		ChainRetry(Supplier<ParsingResult> before, Supplier<ParsingResult> after) {
			this.before = before;
			this.after = after;
		}

		@Override
		public ParsingResult get() {
			ParsingResult retryResult = before.get();
			// if the parse succeeded, either make another chain with more retries from before, or just have them
			// retry after
			if(retryResult.getResult() != null) {
				return new ParsingResult(
						retryResult.getResult(),
						retryResult.getRetry() != null ?
								new ChainRetry(retryResult.getRetry(), after)
								: after);
			}
			// if before fails, try after immediately
			return after.get();
		}
	}

	private static class BranchRetry implements Supplier<ParsingResult> {

		private final LexicalContext.Mark mark;
		private final GrammarExecuteVisitor visitor;
		private final List<? extends Grammar<? extends SourceLocatable>> branches;

		BranchRetry(LexicalContext.Mark mark, GrammarExecuteVisitor visitor, List<? extends Grammar<? extends SourceLocatable>> branches) {
			this.mark = mark;
			this.visitor = visitor;
			this.branches = branches;
		}

		@Override
		public ParsingResult get() {
			for(int i = 0; i < branches.size()-1; ++i){
				visitor.lexicalContext.restore(mark);
				ParsingResult branchResult = visitor.tryMemoize(branches.get(i));
				if(branchResult.getResult() != null) {
					return new ParsingResult(
							branchResult.getResult(),
							branchResult.getRetry() != null ?
									new ChainRetry(branchResult.getRetry(), new BranchRetry(
											mark, visitor, branches.subList(i+1, branches.size())))
									: new BranchRetry(mark, visitor, branches.subList(i+1, branches.size())));
				}
				assert branchResult.getRetry() == null;
			}
			// on the last branch, don't even bother setting up retries. either it fails with no retry or succeeds
			// with its own retries
			visitor.lexicalContext.restore(mark);
			return visitor.tryMemoize(branches.get(branches.size()-1));
		}
	}

	@Override
	public <GrammarResult extends SourceLocatable> ParsingResult visit(BranchGrammar<GrammarResult> branchGrammar) throws RuntimeException {
		List<? extends Grammar<? extends GrammarResult>> branches = branchGrammar.getBranches();
		if(branches.isEmpty()) return new ParsingResult(null, null);
		return new BranchRetry(lexicalContext.mark(), this, branches).get();
	}

	@Override
	public ParsingResult visit(EmptySequenceGrammar emptySequenceGrammar) throws RuntimeException {
		return new ParsingResult(new Located<Void>(SourceLocation.unknown(), null), null);
	}

	private static final class SequenceRetry implements Supplier<ParsingResult> {
		private final Function<SourceLocatable, ParsingResult> executor;
		private final ParsingResult previousResult;
		private final Supplier<ParsingResult> partRetry;
		private final BiFunction<SourceLocatable, SourceLocatable, SourceLocatable> combinator;

		public SequenceRetry(Function<SourceLocatable, ParsingResult> executor, ParsingResult previousResult, Supplier<ParsingResult> partRetry, BiFunction<SourceLocatable, SourceLocatable, SourceLocatable> combinator) {
			this.executor = executor;
			this.previousResult = previousResult;
			this.partRetry = partRetry;
			this.combinator = combinator;
		}

		@Override
		public ParsingResult get() {
			ParsingResult partResult = partRetry.get();
			ParsingResult prevResult = previousResult;
			while(partResult.getResult() == null) {
				if(prevResult.getRetry() == null) {
					assert partResult.getRetry() == null;
					return partResult;
				}
				prevResult = prevResult.getRetry().get();
				if(prevResult.getResult() == null) {
					assert prevResult.getRetry() == null;
					return prevResult;
				}
				partResult = executor.apply(prevResult.getResult());
				if (partResult.getResult() != null) {
					break;
				}
			}

			Located<?> prevResultVal = (Located<?>)prevResult.getResult();
			SourceLocatable currentResult = combinator.apply(partResult.getResult(), prevResultVal);

			if(prevResult.getRetry() == null) {
				if(partResult.getRetry() != null) {
					// if our current part has retries but prev doesn't, use a mapping retry to just keep replacing
					// the current part's result(s) with the previous (and updating the previous result's source location)
					return new ParsingResult(
							currentResult,
							new MappingRetry(
									newPartResult -> combinator.apply(newPartResult, prevResultVal),
									partResult.getRetry()));
				}else{
					return new ParsingResult(currentResult, null);
				}
			}

			return new ParsingResult(
					currentResult,
					new SequenceRetry(
							executor,
							prevResult,
							partResult.getRetry() != null ?
									partResult.getRetry()
									: () -> new ParsingResult(null, null),
							combinator));
		}
	}

	@Override
	public <Dropped extends SourceLocatable, Rest extends EmptyHeterogenousList> ParsingResult visit(DropSequenceGrammar<Dropped, Rest> dropSequenceGrammar) {
		ParsingResult restResult = tryMemoize(dropSequenceGrammar.getPrevious());
		if(restResult.getResult() == null) {
			assert restResult.getRetry() == null;
			return restResult;
		}
		return new SequenceRetry(
				ignored -> tryMemoize(dropSequenceGrammar.getDropped()),
				restResult,
				() -> tryMemoize(dropSequenceGrammar.getDropped()),
				(part, rest) -> {
					Located<?> restV = (Located<?>)rest;
					return new Located<>(rest.getLocation().combine(part.getLocation()), restV.getValue());
				})
				.get();
	}

	@Override
	public <Part extends SourceLocatable, Rest extends EmptyHeterogenousList> ParsingResult visit(PartSequenceGrammar<Part, Rest> partSequenceGrammar) {
		ParsingResult restResult = tryMemoize(partSequenceGrammar.getPrevGrammar());
		if(restResult.getResult() == null) {
			assert restResult.getRetry() == null;
			return restResult;
		}
		return new SequenceRetry(
				ignored -> tryMemoize(partSequenceGrammar.getCurrent()),
				restResult,
				() -> tryMemoize(partSequenceGrammar.getCurrent()),
				(part, rest) -> {
					Located<? extends EmptyHeterogenousList> restV =
							(Located<? extends EmptyHeterogenousList>)rest;
					return new Located<>(
							part.getLocation().combine(rest.getLocation()),
							HeterogenousListTools.cons(part, restV.getValue()));
				})
				.get();
	}

	@Override
	public <GrammarResult extends SourceLocatable, PredecessorResult extends EmptyHeterogenousList> ParsingResult visit(CallGrammar<GrammarResult, PredecessorResult> callGrammar) {
		ParsingResult precedessorResult = tryMemoize(callGrammar.getPredecessor());
		if(precedessorResult.getResult() == null) {
			assert precedessorResult.getRetry() == null;
			return precedessorResult;
		}
		Function<SourceLocatable, ParsingResult> executor = prevResult ->
				new GrammarExecuteVisitor(
						lexicalContext,
						callGrammar
								.getMappingGenerator()
								.apply(new ParseInfo<>(
										(Located<PredecessorResult>) prevResult,
										variableMap))
								.freeze(),
						failures,
						memoizeTable).tryMemoize(callGrammar.getTarget());
		return new SequenceRetry(
				executor,
				precedessorResult,
				() -> executor.apply(precedessorResult.getResult()),
				(part, rest) -> {
					Located<? extends EmptyHeterogenousList> restV =
							(Located<? extends EmptyHeterogenousList>)rest;
					return new Located<>(
							part.getLocation().combine(rest.getLocation()),
							HeterogenousListTools.cons(part, restV.getValue()));
				})
				.get();
	}

	@Override
	public <GrammarResult extends SourceLocatable> ParsingResult visit(CutGrammar<GrammarResult> cutGrammar) throws RuntimeException {
		ParsingResult result = tryMemoize(cutGrammar.getToCut());
		return new ParsingResult(result.getResult(), null);
	}

	private static final class PredicateRetry implements Supplier<ParsingResult> {
		private final Supplier<ParsingResult> retry;
		private final Predicate<ParseInfo<SourceLocatable>> predicate;
		private final FrozenVariableMap variableMap;

		public PredicateRetry(Supplier<ParsingResult> retry, Predicate<? extends ParseInfo<? extends SourceLocatable>> predicate, FrozenVariableMap variableMap) {
			this.retry = retry;
			this.predicate = (Predicate<ParseInfo<SourceLocatable>>)predicate;
			this.variableMap = variableMap;
		}

		@Override
		public ParsingResult get() {
			ParsingResult retryResult = retry.get();
			while(retryResult.getResult() != null){
				if(predicate.test(new ParseInfo<>(retryResult.getResult(), variableMap))){
					return new ParsingResult(
							retryResult.getResult(),
							retryResult.getRetry() != null ?
									new PredicateRetry(retryResult.getRetry(), predicate, variableMap)
									: null);
				}else{
					if(retryResult.getRetry() != null) {
						// try to see if the next alternative passes the filter
						retryResult = retryResult.getRetry().get();
					}else{
						return new ParsingResult(null, null);
					}
				}
			}
			assert retryResult.getRetry() == null;
			return retryResult;
		}
	}

	@Override
	public <GrammarResult extends SourceLocatable> ParsingResult visit(PredicateGrammar<GrammarResult> predicateGrammar) throws RuntimeException {
		ParsingResult prevResult = predicateGrammar.getToFilter().accept(this);
		return new PredicateRetry(() -> prevResult, predicateGrammar.getPredicate(), variableMap).get();
	}

	@Override
	public <GrammarResult extends SourceLocatable> ParsingResult visit(RejectGrammar<GrammarResult> rejectGrammar) throws RuntimeException {
		Grammar<GrammarResult> toReject = rejectGrammar.getToReject();
		LexicalContext.Mark mark = lexicalContext.mark();
		ParsingResult result = toReject.accept(new GrammarExecuteVisitor(lexicalContext, variableMap, new TreeMap<>(), memoizeTable));
		lexicalContext.restore(mark);
		if(result.getResult() != null) {
			// if the grammar succceeds in any way, fail
			addFailure(ParseFailure.rejectFailure(toReject));
			return new ParsingResult(null, null);
		}else{
			return new ParsingResult(new Located<Void>(lexicalContext.getSourceLocation(), null), null);
		}
	}

	@Override
	public ParsingResult visit(EOFGrammar eofGrammar) throws RuntimeException {
		if(lexicalContext.isEOF()) {
			return new ParsingResult(new Located<>(lexicalContext.getSourceLocation(), null), null);
		}else{
			addFailure(ParseFailure.eofMatchFailure());
			return new ParsingResult(null, null);
		}
	}
}
