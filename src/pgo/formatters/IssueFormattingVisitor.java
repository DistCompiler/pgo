package pgo.formatters;

import pgo.errors.IssueVisitor;
import pgo.errors.IssueWithContext;
import pgo.model.mpcal.ModularPlusCalArchetype;
import pgo.model.mpcal.ModularPlusCalInstance;
import pgo.model.mpcal.ModularPlusCalNodeFormattingVisitor;
import pgo.model.pcal.PlusCalCall;
import pgo.model.pcal.PlusCalMacro;
import pgo.model.pcal.PlusCalProcedure;
import pgo.model.type.*;
import pgo.parser.ParseFailure;
import pgo.trans.intermediate.*;
import pgo.trans.passes.codegen.pluscal.RefMismatchIssue;
import pgo.trans.passes.expansion.*;
import pgo.trans.passes.parse.option.OptionParserIssue;
import pgo.trans.passes.parse.pcal.PlusCalParserIssue;
import pgo.trans.passes.parse.tla.ParsingIssue;
import pgo.trans.passes.scope.*;
import pgo.trans.passes.type.TypeInferenceFailureIssue;
import pgo.trans.passes.validation.*;
import pgo.util.Origin;
import pgo.util.SourceLocation;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
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
	public Void visit(NonRefParamModification nonRefParamModification) throws IOException {
		out.write("non-ref ");
		nonRefParamModification.getDeclarationUID().accept(new DerivedFormattingVisitor(out));
		out.write(" is modified in archetype body");
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
	public Void visit(NoMatchingFieldIssue noMatchingFieldIssue) throws IOException {
		out.write("record ");
		noMatchingFieldIssue.getRecord().accept(new PGoTypeFormattingVisitor(out));
		out.write(" has no field with name ");
		out.write(noMatchingFieldIssue.getFieldName());
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
	public Void visit(InfiniteTypeIssue infiniteTypeIssue) throws IOException {
		out.write("unifying ");
		infiniteTypeIssue.getLhs().accept(new PGoTypeFormattingVisitor(out));
		out.write(" and ");
		infiniteTypeIssue.getRhs().accept(new PGoTypeFormattingVisitor(out));
		out.write(" leads to infinite types");
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
	public Void visit(UnsatisfiableConstraintIssue unsatisfiableConstraintIssue) throws IOException {
		out.write("could not unify ");
		unsatisfiableConstraintIssue.getLhs().accept(new DerivedFormattingVisitor(out));
		out.write(" and ");
		unsatisfiableConstraintIssue.getRhs().accept(new DerivedFormattingVisitor(out));
		out.write("; ");
		List<Origin> origins = new ArrayList<>(unsatisfiableConstraintIssue.getLhs().getOrigins());
		origins.addAll(unsatisfiableConstraintIssue.getRhs().getOrigins());
		(new DerivedFormattingVisitor(out)).writeOrigins(origins);
		return null;
	}

	@Override
	public Void visit(TypeInferenceFailureIssue typeInferenceFailureIssue) throws IOException {
		out.write("could not infer type for ");
		typeInferenceFailureIssue.getUID().accept(new DerivedFormattingVisitor(out));
		out.write("; got ");
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
		out.write(Integer.toString(archetype.getLocation().getStartLine()));
		out.write(" column ");
		out.write(Integer.toString(archetype.getLocation().getStartColumn()));
		out.write(" requires ");
		out.write(Integer.toString(archetype.getParams().size()));
		out.write(" parameters while instance statement at line ");
		ModularPlusCalInstance instance = instanceArgumentCountMismatchIssue.getModularPlusCalInstance();
		out.write(Integer.toString(instance.getLocation().getStartLine()));
		out.write(" column ");
		out.write(Integer.toString(instance.getLocation().getStartColumn()));
		out.write(" referencing it provides ");
		out.write(Integer.toString(instance.getArguments().size()));
		out.write(" arguments");
		return null;
	}

	@Override
	public Void visit(InconsistentInstantiationIssue inconsistentInstantiationIssue) throws IOException {
		out.write("instantiation ");
		inconsistentInstantiationIssue.getInstance().accept(new ModularPlusCalNodeFormattingVisitor(out));
		out.write(" is inconsistent with ");
		inconsistentInstantiationIssue.getConflict().accept(new ModularPlusCalNodeFormattingVisitor(out));
		out.write(" (one maps function calls, the other does not)");

		return null;
	}

	@Override
	public Void visit(RefMismatchIssue refMismatchIssue) throws IOException {
		out.write("mismatch in call between ");
		refMismatchIssue.getParam().accept(new PlusCalNodeFormattingVisitor(out));
		out.write(" and ");
		refMismatchIssue.getValue().accept(new TLANodeFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(InvalidArchetypeResourceUsageIssue invalidArchetypeResourceUsageIssue) throws IOException {
		String usedAs, mappedAs;

		if (invalidArchetypeResourceUsageIssue.isFunction()) {
			usedAs = "variable";
			mappedAs = "function";
		} else {
			usedAs = "function";
			mappedAs = "variable";
		}

		out.write("invalid use of archetype resource ");
		invalidArchetypeResourceUsageIssue.getVarUID().accept(new DerivedFormattingVisitor(out));
		out.write(": used as a " + usedAs + " but mapped as a " + mappedAs + ". In statement: ");
		invalidArchetypeResourceUsageIssue.getStatement().accept(new PlusCalStatementFormattingVisitor(out));

		return null;
	}

	@Override
	public Void visit(ProcedureCallArgumentCountMismatchIssue procedureCallArgumentCountMismatchIssue) throws IOException {
		out.write("procedure ");
		PlusCalProcedure procedure = procedureCallArgumentCountMismatchIssue.getProcedure();
		out.write(procedure.getName());
		out.write(" defined at line ");
		out.write(Integer.toString(procedure.getLocation().getStartLine()));
		out.write(" column ");
		out.write(Integer.toString(procedure.getLocation().getStartColumn()));
		out.write(" requires ");
		out.write(Integer.toString(procedure.getParams().size()));
		out.write(" parameters while procedure call at line ");
		PlusCalCall plusCalCall = procedureCallArgumentCountMismatchIssue.getCall();
		out.write(Integer.toString(plusCalCall.getLocation().getStartLine()));
		out.write(" column ");
		out.write(Integer.toString(plusCalCall.getLocation().getStartColumn()));
		out.write(" referencing it provides ");
		out.write(Integer.toString(plusCalCall.getArguments().size()));
		out.write(" arguments");
		return null;
	}

	@Override
	public Void visit(ArchetypeNotFoundIssue archetypeNotFoundIssue) throws IOException {
		out.write("could not find archetype with name ");
		out.write(archetypeNotFoundIssue.getArchetypeName());
		out.write(" from ");
		archetypeNotFoundIssue.getOrigin().accept(new OriginFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(VariableMappedMultipleTimesIssue variableMappedMultipleTimesIssue) throws IOException {
		out.write("global ");
		variableMappedMultipleTimesIssue.getVarUID().accept(new DerivedFormattingVisitor(out));
		out.write(" is used multiple time in ");
		variableMappedMultipleTimesIssue.getInstance().accept(new OriginFormattingVisitor(out));
		return null;
	}
}

