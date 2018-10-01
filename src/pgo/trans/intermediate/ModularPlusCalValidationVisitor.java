package pgo.trans.intermediate;

import pgo.errors.IssueContext;
import pgo.model.mpcal.*;
import pgo.model.pcal.*;
import pgo.model.tla.TLAUnit;
import pgo.trans.passes.validation.StatementVariableAccessValidationVisitor;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Stream;

/**
 * Validates that the Modular PlusCal specification is valid according to the restrictions
 * imposed by the language (documented at https://github.com/UBC-NSS/pgo/wiki/Modular-PlusCal).
 */
public class ModularPlusCalValidationVisitor extends ModularPlusCalBlockVisitor<Void, RuntimeException> {
	private final IssueContext ctx;
	private final Set<String> macrosInScope;
	private final Set<String> proceduresInScope;

	public ModularPlusCalValidationVisitor(IssueContext ctx) {
		this.ctx = ctx;
		this.macrosInScope = new HashSet<>();
		this.proceduresInScope = new HashSet<>();
	}

	public Void visit(ModularPlusCalBlock modularPlusCalBlock) {
		modularPlusCalBlock.getMacros().forEach(m -> macrosInScope.add(m.getName()));
		modularPlusCalBlock.getProcedures().forEach(p -> proceduresInScope.add(p.getName()));

		for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
			archetype.accept(this);
		}

		for (ModularPlusCalMappingMacro mappingMacro : modularPlusCalBlock.getMappingMacros()) {
			mappingMacro.accept(this);
		}

		for (PlusCalMacro macro : modularPlusCalBlock.getMacros()) {
			macro.accept(this);
		}

		for (PlusCalProcedure procedure : modularPlusCalBlock.getProcedures()) {
			procedure.accept(this);
		}

		if (modularPlusCalBlock.getProcesses() instanceof PlusCalSingleProcess) {
			PlusCalSingleProcess singleProcess = (PlusCalSingleProcess) modularPlusCalBlock.getProcesses();
			singleProcess.accept(this);
		} else if (modularPlusCalBlock.getProcesses() instanceof PlusCalMultiProcess) {
			PlusCalMultiProcess multiProcess = (PlusCalMultiProcess) modularPlusCalBlock.getProcesses();
			multiProcess.accept(this);
		}

		return null;
	}

	/*
	* Archetypes in Modular PlusCal must obey the following rules and restrictions:
	*
	*   * Same labelling rules of vanilla PlusCal apply (see C-syntax manual, section 3.7)
	*   * Only local or `ref` variables can be assigned to
	*/
	public Void visit(ModularPlusCalArchetype modularPlusCalArchetype) {
		Set<String> localMacrosInScope = new HashSet<>(macrosInScope);
		Set<String> localProceduresInScope = new HashSet<>(proceduresInScope);
		Set<String> variablesInScope = new HashSet<>();
		Set<String> refVariablesInScope = new HashSet<>();
		StatementVariableAccessValidationVisitor.validateDeclarations(
				ctx, localMacrosInScope, localProceduresInScope, variablesInScope, refVariablesInScope,
				Stream.concat(modularPlusCalArchetype.getArguments().stream(),
						modularPlusCalArchetype.getVariables().stream()));

		// guaranteed to exist at the parsing stage
		PlusCalStatement firstStatement = modularPlusCalArchetype.getBody().get(0);
		checkLabeled(firstStatement);

		ModularPlusCalLabelingRulesVisitor visitor = new ModularPlusCalLabelingRulesVisitor(ctx);
		StatementVariableAccessValidationVisitor accessValidationVisitor =
				new StatementVariableAccessValidationVisitor(
						ctx, localMacrosInScope, localProceduresInScope, variablesInScope, refVariablesInScope);
		for (PlusCalStatement statement : modularPlusCalArchetype.getBody()) {
			statement.accept(visitor);
			statement.accept(accessValidationVisitor);
		}

		// TODO: validate archetypes

		return null;
	}

	public Void visit(ModularPlusCalInstance modularPlusCalInstance) {
		return null;
	}

	public Void visit(ModularPlusCalMappingMacro modularPlusCalMappingMacro) {
		// TODO: validate mapping macros
		return null;
	}

	public Void visit(PlusCalMacro plusCalMacro) {
		ModularPlusCalLabelingRulesVisitor visitor =
				new ModularPlusCalLabelingRulesVisitor(this.ctx, false);

		// visit every statement of the macro, collecting an error in case a label
		// is found within
		for (PlusCalStatement statement : plusCalMacro.getBody()) {
			statement.accept(visitor);
		}

		// TODO: validate macros
		return null;
	}

	public Void visit(PlusCalProcedure plusCalProcedure) {
		PlusCalStatement firstStatement = plusCalProcedure.getBody().get(0);
		checkLabeled(firstStatement);

		ModularPlusCalLabelingRulesVisitor visitor = new ModularPlusCalLabelingRulesVisitor(this.ctx);
		for (PlusCalStatement statement : plusCalProcedure.getBody()) {
			statement.accept(visitor);
		}

		// TODO: validate procedures
		return null;
	}

	public Void visit(PlusCalSingleProcess plusCalSingleProcess) {
		PlusCalStatement firstStatement = plusCalSingleProcess.getBody().get(0);
		checkLabeled(firstStatement);

		ModularPlusCalLabelingRulesVisitor visitor = new ModularPlusCalLabelingRulesVisitor(this.ctx);
		for (PlusCalStatement statement : plusCalSingleProcess.getBody()) {
			statement.accept(visitor);
		}

		// TODO: validate single process
		return null;
	}

	public Void visit(PlusCalMultiProcess plusCalMultiProcess) {
		for (PlusCalProcess process : plusCalMultiProcess.getProcesses()) {
			PlusCalStatement firstStatement = process.getBody().get(0);
			checkLabeled(firstStatement);

			ModularPlusCalLabelingRulesVisitor visitor = new ModularPlusCalLabelingRulesVisitor(this.ctx);
			for (PlusCalStatement statement : process.getBody()) {
				statement.accept(visitor);
			}

			// TODO: validate PlusCal processes
		}

		return null;
	}

	public Void visit(TLAUnit tlaUnit) {
		// TODO: validate TLA+ units

		return null;
	}

	private Void checkLabeled(PlusCalStatement statement) {
		boolean isLabeled = statement.accept(new PlusCalFirstStatementLabeledVisitor());

		if (!isLabeled) {
			ctx.error(new MissingLabelIssue(statement));
		}

		return null;
	}
}