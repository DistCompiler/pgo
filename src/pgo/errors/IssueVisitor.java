package pgo.errors;

import pgo.model.type.UnsatisfiableConstraintIssue;
import pgo.trans.intermediate.*;

public abstract class IssueVisitor<T, E extends Throwable> {

	public abstract T visit(IssueWithContext issueWithContext) throws E;
	public abstract T visit(ScopeConflictIssue scopeConflictIssue) throws E;
	public abstract T visit(ModuleNotFoundIssue moduleNotFoundIssue) throws E;
	public abstract T visit(TLALexerIssue tlaLexerIssue) throws E;
	public abstract T visit(DanglingReferenceIssue danglingReferenceIssue) throws E;
	public abstract T visit(IOErrorIssue ioErrorIssue) throws E;
	public abstract T visit(TLAParserIssue tlaParserIssue) throws E;
	public abstract T visit(NoModulesFoundInFileIssue noModulesFoundInFileIssue) throws E;
	public abstract T visit(ModuleSubstitutionNotFound moduleSubstitutionNotFound) throws E;
	public abstract T visit(CircularModuleReferenceIssue circularModuleReferenceIssue) throws E;
	public abstract T visit(UnsupportedFeatureIssue unsupportedFeatureIssue) throws E;
	public abstract T visit(UnresolvableMacroCallIssue unresolvableMacroCallIssue) throws E;
	public abstract T visit(MacroArgumentCountMismatchIssue macroArgumentCountMismatchIssue) throws E;
	public abstract T visit(RecursiveMacroCallIssue recursiveMacroCallIssue) throws E;
	public abstract T visit(MacroArgumentInnerScopeConflictIssue macroArgumentInnerScopeConflictIssue) throws E;
	public abstract T visit(MultiplyDeclaredLabelIssue multiplyDeclaredLabelIssue) throws E;
	public abstract T visit(MacroNameConflictIssue macroNameConflictIssue) throws E;
	public abstract T visit(UnsatisfiableConstraintIssue unsatisfiableConstraintIssue) throws E;
	public abstract T visit(ProcedureNotFoundIssue procedureNotFoundIssue) throws E;

}
