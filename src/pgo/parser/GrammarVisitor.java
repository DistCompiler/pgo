package pgo.parser;

import pgo.util.SourceLocatable;

public abstract class GrammarVisitor<Result, Except extends Throwable> {
	public abstract Result visit(PatternGrammar patternGrammar) throws Except;
	public abstract <GrammarPredecessorResult extends SourceLocatable, GrammarResult extends SourceLocatable> Result visit(MappingGrammar<GrammarPredecessorResult,GrammarResult> mappingGrammar) throws Except;
	public abstract <GrammarResult extends SourceLocatable> Result visit(FixPointGrammar<GrammarResult> fixPointGrammar) throws Except;
	public abstract <GrammarResult extends SourceLocatable> Result visit(ReferenceGrammar<GrammarResult> referenceGrammar) throws Except;
	public abstract Result visit(StringGrammar stringGrammar) throws Except;
	public abstract <GrammarResult extends SourceLocatable> Result visit(BranchGrammar<GrammarResult> branchGrammar) throws Except;
	public abstract Result visit(SequenceGrammar sequenceGrammar) throws Except;
	public abstract <GrammarResult extends SourceLocatable> Result visit(AssignmentGrammar<GrammarResult> assignmentGrammar) throws Except;
	public abstract <GrammarResult extends SourceLocatable> Result visit(PredicateGrammar<GrammarResult> predicateGrammar) throws Except;
	public abstract <GrammarResult extends SourceLocatable> Result visit(RejectGrammar<GrammarResult> rejectGrammar) throws Except;
	public abstract Result visit(EOFGrammar eofGrammar) throws Except;
	public abstract <GrammarResult extends SourceLocatable> Result visit(ArgumentGrammar<GrammarResult> argumentGrammar) throws Except;
	public abstract <GrammarResult extends SourceLocatable> Result visit(CallGrammar<GrammarResult> callGrammar) throws Except;
}
