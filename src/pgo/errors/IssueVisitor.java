package pgo.errors;

import pgo.trans.intermediate.CircularModuleReferenceIssue;
import pgo.trans.intermediate.DanglingReferenceIssue;
import pgo.trans.intermediate.IOErrorIssue;
import pgo.trans.intermediate.MacroArgumentCountMismatchIssue;
import pgo.trans.intermediate.MacroArgumentInnerScopeConflictIssue;
import pgo.trans.intermediate.MacroNameConflictIssue;
import pgo.trans.intermediate.ModuleNotFoundIssue;
import pgo.trans.intermediate.ModuleSubstitutionNotFound;
import pgo.trans.intermediate.MultiplyDeclaredLabelIssue;
import pgo.trans.intermediate.NoModulesFoundInFileIssue;
import pgo.trans.intermediate.RecursiveMacroCallIssue;
import pgo.trans.intermediate.ScopeConflictIssue;
import pgo.trans.intermediate.TLALexerIssue;
import pgo.trans.intermediate.TLAParserIssue;
import pgo.trans.intermediate.UnresolvableMacroCallIssue;
import pgo.trans.intermediate.UnsupportedFeatureIssue;

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

}
