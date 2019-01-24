package pgo.formatters;

import pgo.errors.IssueVisitor;
import pgo.errors.IssueWithContext;
import pgo.model.mpcal.ModularPlusCalArchetype;
import pgo.model.mpcal.ModularPlusCalInstance;
import pgo.model.pcal.PlusCalMacro;
import pgo.model.type.BacktrackingFailureIssue;
import pgo.model.type.PGoTypePolymorphicConstraint;
import pgo.model.type.UnrealizableTypeIssue;
import pgo.model.type.UnsatisfiableConstraintIssue;
import pgo.parser.ParseFailure;
import pgo.trans.intermediate.*;
import pgo.trans.passes.expansion.*;
import pgo.trans.passes.parse.tla.ParsingIssue;
import pgo.trans.passes.scope.MultipleMappingIssue;
import pgo.trans.passes.type.TypeInferenceFailureIssue;
import pgo.trans.passes.validation.LabelNotAllowedIssue;
import pgo.trans.passes.validation.MissingLabelIssue;
import pgo.trans.passes.validation.ReservedLabelNameIssue;
import pgo.trans.passes.validation.StatementNotAllowedIssue;
import pgo.util.SourceLocation;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Map;
import java.util.Set;

public class IssueFormattingVisitor extends IssueVisitor<Void, IOException> {
	private IndentingWriter out;

	public IssueFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(IssueWithContext issueWithContext) throws IOException {
		issueWithContext.getContext().accept(new ContextFormattingVisitor(out));
		try (IndentingWriter.Indent ignored = out.indent()) {
			out.newLine();
			issueWithContext.getIssue().accept(this);
		}
		return null;
	}

	@Override
	public Void visit(OptionParserIssue optionParserIssue) throws IOException {
		out.write("unable to parse options: ");
		out.write(optionParserIssue.getMessage());
		return null;
	}

	@Override
	public Void visit(PlusCalParserIssue plusCalParserIssue) throws IOException {
		out.write("unable to parse PlusCal code: ");
		out.write(plusCalParserIssue.getMessage());
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
		try (IndentingWriter.Indent ignored = out.indent()) {
			for (Path path : moduleNotFoundIssue.getPathsChecked()) {
				out.newLine();
				out.write("- ");
				out.write(path.toString());
			}
		}
		return null;
	}

	@Override
	public Void visit(DanglingReferenceIssue danglingReferenceIssue) throws IOException {
		out.write("could not resolve ");
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
	public Void visit(ParsingIssue parsingIssue) throws IOException {
		Map.Entry<SourceLocation, Set<ParseFailure>> lastEntry = parsingIssue.getError().lastEntry();
		out.write("could not parse " + parsingIssue.getLanguage() + " at " + lastEntry.getKey() + ": ");
		try (IndentingWriter.Indent ignored = out.indent()) {
			Set<ParseFailure> lastFailures = lastEntry.getValue();
			for (ParseFailure f : lastFailures) {
				out.newLine();
				out.write(f.toString());
			}
		}
		return null;
	}

	@Override
	public Void visit(NoModulesFoundInFileIssue noModulesFoundInFileIssue) throws IOException {
		out.write("file does not contain any TLA modules");
		return null;
	}

	@Override
	public Void visit(ModuleSubstitutionNotFoundIssue moduleSubstitutionNotFoundIssue) throws IOException {
		out.write("module instantiation provided a substitution (");
		out.write(moduleSubstitutionNotFoundIssue.getFrom().getId());
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
		PlusCalMacro macro = macroArgumentCountMismatchIssue.getMacro();
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
	public Void visit(MultipleMappingIssue multipleMappingIssue) throws IOException {
		out.write("mappings ");
		multipleMappingIssue.getFirst().accept(new OriginFormattingVisitor(out));
		out.write(" and ");
		multipleMappingIssue.getSecond().accept(new OriginFormattingVisitor(out));
		out.write(" conflict");
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

	@Override
	public Void visit(BacktrackingFailureIssue backtrackingFailureIssue) throws IOException {
		PGoTypePolymorphicConstraint polymorphicConstraint = backtrackingFailureIssue.getPolymorphicConstraint();
		out.write("could not satisfy ");
		polymorphicConstraint.accept(new DerivedFormattingVisitor(out));
		out.write("; constraint is ");
		out.write(polymorphicConstraint.toString());
		return null;
	}

	@Override
	public Void visit(UnrealizableTypeIssue unrealizableTypeIssue) throws IOException {
		out.write("could not realize ");
		unrealizableTypeIssue.getType().accept(new DerivedFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(UnsatisfiableConstraintIssue unsatisfiableConstraintIssue) throws IOException {
		out.write("could not unify ");
		unsatisfiableConstraintIssue.getLhs().accept(new DerivedFormattingVisitor(out));
		out.write(" and ");
		unsatisfiableConstraintIssue.getRhs().accept(new DerivedFormattingVisitor(out));
		out.write("; ");
		unsatisfiableConstraintIssue.getConstraint().accept(new DerivedFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TypeInferenceFailureIssue typeInferenceFailureIssue) throws IOException {
		out.write("could not infer type for ");
		typeInferenceFailureIssue.getUID().accept(new DerivedFormattingVisitor(out));
		out.write("; got");
		typeInferenceFailureIssue.getType().accept(new DerivedFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(ProcedureNotFoundIssue procedureNotFoundIssue) throws IOException {
		out.write("could not find procedure with name ");
		out.write(procedureNotFoundIssue.getProcedureName());
		out.write(" from ");
		procedureNotFoundIssue.getOrigin().accept(new OriginFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(ConstantWithNoValueIssue constantWithNoValueIssue) throws IOException {
		out.write("could not find value for constant ");
		out.write(constantWithNoValueIssue.getName());
		out.write(" in configuration file; ");
		constantWithNoValueIssue.getDefinition().accept(new OriginFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(MissingLabelIssue missingLabelIssue) throws IOException {
		out.write("Label required in statement: ");
		missingLabelIssue.getStatement().accept(new OriginFormattingVisitor(out));

		return null;
	}

	@Override
	public Void visit(LabelNotAllowedIssue labelNotAllowedIssue) throws IOException {
		out.write("Label not allowed in statement: ");
		labelNotAllowedIssue.getStatement().accept(new OriginFormattingVisitor(out));

		return null;
	}

	@Override
	public Void visit(ReservedLabelNameIssue reservedLabelNameIssue) throws IOException {
		out.write("Label not allowed in statement: ");
		reservedLabelNameIssue.getStatement().accept(new OriginFormattingVisitor(out));

		return null;
	}

	@Override
	public Void visit(StatementNotAllowedIssue statementNotAllowedIssue) throws IOException {
		out.write("Statement not allowed in this context: ");
		statementNotAllowedIssue.getStatement().accept(new OriginFormattingVisitor(out));

		return null;
	}

	@Override
	public Void visit(InstanceArgumentCountMismatchIssue instanceArgumentCountMismatchIssue) throws IOException {
		out.write("archetype ");
		ModularPlusCalArchetype archetype = instanceArgumentCountMismatchIssue.getModularPlusCalArchetype();
		out.write(archetype.getName());
		out.write(" defined at line ");
		out.write(archetype.getLocation().getStartLine());
		out.write(" column ");
		out.write(archetype.getLocation().getStartColumn());
		out.write(" requires ");
		out.write(archetype.getParams().size());
		out.write(" argument(s) while instance statement at line ");
		ModularPlusCalInstance instance = instanceArgumentCountMismatchIssue.getModularPlusCalInstance();
		out.write(instance.getLocation().getStartLine());
		out.write(" column ");
		out.write(instance.getLocation().getStartColumn());
		out.write(" referencing it provides ");
		out.write(instance.getArguments().size());
		out.write(" parameters");
		return null;
	}
}

