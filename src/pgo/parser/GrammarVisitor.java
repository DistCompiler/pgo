package pgo.parser;

import pgo.util.SourceLocatable;

public abstract class GrammarVisitor<Result, Except extends Throwable> {
	public abstract Result visit(PatternGrammar patternGrammar) throws Except;
	public abstract <GrammarPredecessorResult extends SourceLocatable, GrammarResult extends SourceLocatable> Result visit(MappingGrammar<GrammarPredecessorResult,GrammarResult> mappingGrammar) throws Except;
	public abstract <GrammarResult extends SourceLocatable> Result visit(ReferenceGrammar<GrammarResult> referenceGrammar) throws Except;
	public abstract Result visit(StringGrammar stringGrammar) throws Except;
	public abstract <GrammarResult extends SourceLocatable> Result visit(BranchGrammar<GrammarResult> branchGrammar) throws Except;
	public abstract <GrammarResult extends SourceLocatable> Result visit(PredicateGrammar<GrammarResult> predicateGrammar) throws Except;
	public abstract <GrammarResult extends SourceLocatable> Result visit(RejectGrammar<GrammarResult> rejectGrammar) throws Except;
	public abstract Result visit(EOFGrammar eofGrammar) throws Except;
	public abstract Result visit(EmptySequenceGrammar emptySequenceGrammar);
	public abstract <Dropped extends SourceLocatable, PrevResult extends EmptyHeterogenousList> Result visit(DropSequenceGrammar<Dropped,PrevResult> propSequenceGrammar) throws Except;
	public abstract <Part extends SourceLocatable, PrevResult extends EmptyHeterogenousList> Result visit(PartSequenceGrammar<Part,PrevResult> partSequenceGrammar) throws Except;
	public abstract <GrammarResult extends SourceLocatable, PredecessorResult extends EmptyHeterogenousList> Result visit(CallGrammar<GrammarResult, PredecessorResult> callGrammar);
	public abstract <GrammarResult extends SourceLocatable> Result visit(CutGrammar<GrammarResult> resultCutGrammar) throws Except;
	public abstract <GrammarResult extends SourceLocatable> Result visit(MemoizeGrammar<GrammarResult> memoizeGrammar) throws Except;
}
