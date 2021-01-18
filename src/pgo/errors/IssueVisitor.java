package pgo.errors;

import pgo.model.type.BacktrackingFailureIssue;
import pgo.model.type.NoMatchingFieldIssue;
import pgo.model.type.InfiniteTypeIssue;
import pgo.model.type.UnsatisfiableConstraintIssue;
import pgo.trans.intermediate.IOErrorIssue;
import pgo.trans.intermediate.UnsupportedFeatureIssue;
import pgo.trans.passes.codegen.pluscal.RefMismatchIssue;
import pgo.trans.passes.expansion.*;
import pgo.trans.passes.parse.option.OptionParserIssue;
import pgo.trans.passes.parse.pcal.PlusCalParserIssue;
import pgo.trans.passes.parse.ParsingIssue;
import pgo.trans.passes.type.TypeInferenceFailureIssue;
import pgo.trans.passes.validation.*;

public abstract class IssueVisitor<T, E extends Throwable> {
	public abstract T visit(IssueWithContext issueWithContext) throws E;
	public abstract T visit(OptionParserIssue optionParserIssue) throws E;
	public abstract T visit(PlusCalParserIssue plusCalParserIssue) throws E;
	public abstract T visit(IOErrorIssue ioErrorIssue) throws E;
	public abstract T visit(ParsingIssue parsingIssue) throws E;
	public abstract T visit(NoMatchingFieldIssue noMatchingFieldIssue) throws E;
	public abstract T visit(NonRefParamModification nonRefParamModification) throws E;
	public abstract T visit(CircularModuleReferenceIssue circularModuleReferenceIssue) throws E;
	public abstract T visit(UnsupportedFeatureIssue unsupportedFeatureIssue) throws E;
	public abstract T visit(UnresolvableMacroCallIssue unresolvableMacroCallIssue) throws E;
	public abstract T visit(MacroArgumentCountMismatchIssue macroArgumentCountMismatchIssue) throws E;
	public abstract T visit(RecursiveMacroCallIssue recursiveMacroCallIssue) throws E;
	public abstract T visit(InfiniteTypeIssue infiniteTypeIssue) throws E;
	public abstract T visit(MacroArgumentInnerScopeConflictIssue macroArgumentInnerScopeConflictIssue) throws E;
	public abstract T visit(MacroNameConflictIssue macroNameConflictIssue) throws E;
	public abstract T visit(BacktrackingFailureIssue backtrackingFailureIssue) throws E;
	public abstract T visit(UnsatisfiableConstraintIssue unsatisfiableConstraintIssue) throws E;
	public abstract T visit(TypeInferenceFailureIssue typeInferenceFailureIssue) throws E;
	public abstract T visit(MissingLabelIssue missingLabelIssue) throws E;
	public abstract T visit(LabelNotAllowedIssue labelNotAllowedIssue) throws E;
	public abstract T visit(ReservedLabelNameIssue reservedLabelNameIssue) throws E;
	public abstract T visit(StatementNotAllowedIssue statementNotAllowedIssue) throws E;
	public abstract T visit(InstanceArgumentCountMismatchIssue instanceArgumentCountMismatchIssue) throws E;
	public abstract T visit(InconsistentInstantiationIssue inconsistentInstantiationIssue) throws E;
	public abstract T visit(RefMismatchIssue refMismatchIssue) throws E;
	public abstract T visit(InvalidArchetypeResourceUsageIssue invalidArchetypeResourceUsageIssue) throws E;
	public abstract T visit(VariableMappedMultipleTimesIssue variableMappedMultipleTimesIssue) throws E;
}
