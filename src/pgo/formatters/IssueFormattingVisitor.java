package pgo.formatters;

import pgo.errors.IssueVisitor;
import pgo.errors.IssueWithContext;
import pgo.model.mpcal.ModularPlusCalArchetype;
import pgo.model.mpcal.ModularPlusCalInstance;
import pgo.model.mpcal.ModularPlusCalNodeFormattingVisitor;
import pgo.model.pcal.PlusCalMacro;
import pgo.model.type.*;
import pgo.model.type.constraint.PolymorphicConstraint;
import pgo.trans.intermediate.*;
import pgo.trans.passes.codegen.pluscal.RefMismatchIssue;
import pgo.trans.passes.expansion.*;
import pgo.trans.passes.parse.option.OptionParserIssue;
import pgo.trans.passes.parse.pcal.PlusCalParserIssue;
import pgo.trans.passes.parse.ParsingIssue;
import pgo.trans.passes.type.TypeInferenceFailureIssue;
import pgo.trans.passes.validation.*;
import pgo.util.Origin;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

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
	public Void visit(IOErrorIssue ioErrorIssue) throws IOException {
		out.write("IO Error: ");
		out.write(ioErrorIssue.getError().toString());
		return null;
	}

	@Override
	public Void visit(ParsingIssue parsingIssue) throws IOException {
		out.write("error parsing "+parsingIssue.getLanguage()+": ");
		out.write(parsingIssue.getError().getMessage());
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
	public Void visit(NoMatchingFieldIssue noMatchingFieldIssue) throws IOException {
		out.write("record ");
		noMatchingFieldIssue.getRecord().accept(new TypeFormattingVisitor(out));
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
		out.write("could not find macro [" + unresolvableMacroCallIssue.getMacroCall().getTarget() +
						"] referenced by macro call at line ");
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
		infiniteTypeIssue.getLhs().accept(new TypeFormattingVisitor(out));
		out.write(" and ");
		infiniteTypeIssue.getRhs().accept(new TypeFormattingVisitor(out));
		out.write(" leads to infinite types");
		return null;
	}

	@Override
	public Void visit(MacroArgumentInnerScopeConflictIssue macroArgumentInnerScopeConflictIssue) throws IOException {
		out.write("locally bound identifier at line ");
		out.write(Integer.toString(macroArgumentInnerScopeConflictIssue.getIdentifier().getLocation().getStartLine()));
		out.write(" column ");
		out.write(Integer.toString(macroArgumentInnerScopeConflictIssue.getIdentifier().getLocation().getStartColumn()));
		out.write(" conflicts with PlusCal macro parameter; this will likely not work with the TLC");
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
		PolymorphicConstraint polymorphicConstraint = backtrackingFailureIssue.getPolymorphicConstraint();
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

		out.write("invalid use of archetype resource: used as a " + usedAs + " but mapped as a " + mappedAs + ". In statement: ");
		invalidArchetypeResourceUsageIssue.getStatement().accept(new PlusCalStatementFormattingVisitor(out));

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

