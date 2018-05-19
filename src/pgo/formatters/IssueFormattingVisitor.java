package pgo.formatters;

import java.io.IOException;
import java.nio.file.Path;

import pgo.errors.IssueVisitor;
import pgo.errors.IssueWithContext;
import pgo.model.pcal.Macro;
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

public class IssueFormattingVisitor extends IssueVisitor<Void, IOException> {

	private IndentingWriter out;

	public IssueFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(IssueWithContext issueWithContext) throws IOException {
		issueWithContext.getContext().accept(new ContextFormattingVisitor(out));
		try(IndentingWriter.Indent i_ = out.indent()){
			issueWithContext.getIssue().accept(this);
		}
		return null;
	}

	@Override
	public Void visit(ScopeConflictIssue scopeConflictIssue) throws IOException {
		out.write("scoping conflict between ");
		scopeConflictIssue.getFirst().accept(new OriginFormattingVisitor(out));
		out.write(" and ");
		scopeConflictIssue.getSecond().accept(new OriginFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(ModuleNotFoundIssue moduleNotFoundIssue) throws IOException {
		out.write("TLA module ");
		out.write(moduleNotFoundIssue.getModuleName());
		out.write(" not found; looked in:");
		out.newLine();
		try(IndentingWriter.Indent i_ = out.indent()){
			for(Path path : moduleNotFoundIssue.getPathsChecked()) {
				out.write("- ");
				out.write(path.toString());
			}
		}
		return null;
	}

	@Override
	public Void visit(TLALexerIssue tlaLexerIssue) throws IOException {
		out.write(tlaLexerIssue.getError().toString());
		return null;
	}

	@Override
	public Void visit(DanglingReferenceIssue danglingReferenceIssue) throws IOException {
		out.write("could not resolve symbol ");
		danglingReferenceIssue.getFrom().accept(new OriginFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(IOErrorIssue ioErrorIssue) throws IOException {
		out.write("IO Error: ");
		out.write(ioErrorIssue.getError().toString());
		return null;
	}

	@Override
	public Void visit(TLAParserIssue tlaParserIssue) throws IOException {
		out.write("could not parse TLA: ");
		try(IndentingWriter.Indent i_ = out.indent()){
			out.write(tlaParserIssue.getError().toString());
		}
		return null;
	}

	@Override
	public Void visit(NoModulesFoundInFileIssue noModulesFoundInFileIssue) throws IOException {
		out.write("file does not contain any TLA modules");
		return null;
	}

	@Override
	public Void visit(ModuleSubstitutionNotFound moduleSubstitutionNotFound) throws IOException {
		out.write("module instantiation provided a substitution (");
		out.write(moduleSubstitutionNotFound.getFrom().getId());
		out.write(" that does not match and variables/constants declared by that module");
		return null;
	}

	@Override
	public Void visit(CircularModuleReferenceIssue circularModuleReferenceIssue) throws IOException {
		out.write("encountered circular reference to module ");
		out.write(circularModuleReferenceIssue.getModuleName());
		return null;
	}

	@Override
	public Void visit(UnsupportedFeatureIssue unsupportedFeatureIssue) throws IOException {
		out.write("feature not supported by PGo: ");
		out.write(unsupportedFeatureIssue.getMessage());
		return null;
	}

	@Override
	public Void visit(UnresolvableMacroCallIssue unresolvableMacroCallIssue) throws IOException {
		out.write("could not find macro referenced by macro call at line ");
		out.write(unresolvableMacroCallIssue.getMacroCall().getLocation().getStartLine());
		out.write(" column ");
		out.write(unresolvableMacroCallIssue.getMacroCall().getLocation().getStartColumn());
		return null;
	}

	@Override
	public Void visit(MacroArgumentCountMismatchIssue macroArgumentCountMismatchIssue) throws IOException {
		out.write("macro argument mismatch while calling macro ");
		Macro macro = macroArgumentCountMismatchIssue.getMacro();
		out.write(macro.getName());
		out.write(" defined at line ");
		out.write(macro.getLocation().getStartLine());
		out.write(" column ");
		out.write(macro.getLocation().getStartColumn());
		out.write("from line ");
		out.write(macroArgumentCountMismatchIssue.getMacroCall().getLocation().getStartLine());
		out.write(" column ");
		out.write(macroArgumentCountMismatchIssue.getMacroCall().getLocation().getStartColumn());
		return null;
	}

	@Override
	public Void visit(RecursiveMacroCallIssue recursiveMacroCallIssue) throws IOException {
		out.write("encountered recursive macro call at line ");
		out.write(recursiveMacroCallIssue.getMacroCall().getLocation().getStartLine());
		out.write(" column ");
		out.write(recursiveMacroCallIssue.getMacroCall().getLocation().getStartColumn());
		return null;
	}

	@Override
	public Void visit(MacroArgumentInnerScopeConflictIssue macroArgumentInnerScopeConflictIssue) throws IOException {
		out.write("locally bound identifier at line ");
		out.write(macroArgumentInnerScopeConflictIssue.getIdentifier().getLocation().getStartLine());
		out.write(" column ");
		out.write(macroArgumentInnerScopeConflictIssue.getIdentifier().getLocation().getStartColumn());
		out.write(" conflicts with PlusCal macro parameter; this will likely not work with the TLC");
		return null;
	}

	@Override
	public Void visit(MultiplyDeclaredLabelIssue multiplyDeclaredLabelIssue) throws IOException {
		out.write("label declarations ");
		multiplyDeclaredLabelIssue.getFirst().accept(new OriginFormattingVisitor(out));
		out.write(" and ");
		multiplyDeclaredLabelIssue.getSecond().accept(new OriginFormattingVisitor(out));
		out.write("conflict");
		return null;
	}

	@Override
	public Void visit(MacroNameConflictIssue macroNameConflictIssue) throws IOException {
		out.write("the two macro definitions at line ");
		out.write(macroNameConflictIssue.getFirst().getLocation().getStartLine());
		out.write(" column ");
		out.write(macroNameConflictIssue.getFirst().getLocation().getStartColumn());
		out.write(" and line ");
		out.write(macroNameConflictIssue.getSecond().getLocation().getStartLine());
		out.write(" column ");
		out.write(macroNameConflictIssue.getSecond().getLocation().getStartColumn());
		out.write(" share the same name");
		return null;
	}

}
