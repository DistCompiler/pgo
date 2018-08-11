package pgo.parser;

public interface ParseActionExecutor {
	boolean visit(StringParseAction stringParseAction);
	boolean visit(PatternParseAction patternParseAction);
	boolean visit(FailParseAction failParseAction);
	boolean visit(BranchParseAction branchParseAction);
	boolean visit(MappingParseAction mappingParseAction);
	boolean visit(ReturnParseAction returnParseAction);
	boolean visit(ReferenceParseAction referenceParseAction);
	boolean visit(AssignmentParseAction assignmentParseAction);
	boolean visit(AccumulateLocationsParseAction accumulateLocationsParseAction);
	boolean visit(StoreValueParseAction storeValueParseAction);
	boolean visit(PredicateParseAction predicateParseAction);
	boolean visit(RejectParseAction rejectParseAction);
	boolean visit(EOFParseAction eofParseAction);
	boolean visit(IndirectReferenceParseAction indirectReferenceParseAction);
}
