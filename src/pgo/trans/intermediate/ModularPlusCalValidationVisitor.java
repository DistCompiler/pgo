package pgo.trans.intermediate;

import pgo.errors.IssueContext;
import pgo.model.mpcal.*;
import pgo.model.pcal.*;
import pgo.model.tla.TLAUnit;

/**
 * Validates that the Modular PlusCal specification is valid according to the restrictions
 * imposed by the language (documented at https://github.com/UBC-NSS/pgo/wiki/Modular-PlusCal).
 */
public class ModularPlusCalValidationVisitor extends ModularPlusCalBlockVisitor<Void, RuntimeException> {
    private IssueContext ctx;

    public ModularPlusCalValidationVisitor(IssueContext ctx) {
        this.ctx = ctx;
    }

    public Void visit(ModularPlusCalBlock modularPlusCalBlock) {
        for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
            archetype.accept(this);
        }

        for (ModularPlusCalMappingMacro mappingMacro : modularPlusCalBlock.getMappingMacros()) {
            mappingMacro.accept(this);
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

        for (PlusCalMacro macro : modularPlusCalBlock.getMacros()) {
            macro.accept(this);
        }

        return null;
    }

    /*
    * Archetypes in Modular PlusCal must obey the following rules and restrictions:
    *
    *   * Same labelling rules of vanilla PlusCal apply (see C-syntax manual, section 3.7)
    *   * Only local or `ref` variables can be assigned to
    */
    public  Void visit(ModularPlusCalArchetype modularPlusCalArchetype) {
        // guaranteed to exist at the parsing stage
        PlusCalStatement firstStatement = modularPlusCalArchetype.getBody().get(0);
        checkLabeled(firstStatement);

        ModularPlusCalValidationPlusCalStatementVisitor visitor = new ModularPlusCalValidationPlusCalStatementVisitor(this.ctx);
        for (PlusCalStatement statement : modularPlusCalArchetype.getBody()) {
            statement.accept(visitor);
        }

        // TODO: validate archetypes

        return null;
    }

    public  Void visit(ModularPlusCalInstance modularPlusCalInstance) {
        return null;
    }

    public  Void visit(ModularPlusCalMappingMacro modularPlusCalMappingMacro) {
        // TODO: validate mapping macros
        return null;
    }

    public Void visit(PlusCalMacro plusCalMacro) {
        // TODO: validate macros
        return null;
    }

    public Void visit(PlusCalProcedure plusCalProcedure) {
        PlusCalStatement firstStatement = plusCalProcedure.getBody().get(0);
        checkLabeled(firstStatement);

        ModularPlusCalValidationPlusCalStatementVisitor visitor = new ModularPlusCalValidationPlusCalStatementVisitor(this.ctx);
        for (PlusCalStatement statement : plusCalProcedure.getBody()) {
            statement.accept(visitor);
        }

        // TODO: validate procedures
        return null;
    }

    public Void visit(PlusCalSingleProcess plusCalSingleProcess) {
        PlusCalStatement firstStatement = plusCalSingleProcess.getBody().get(0);
        checkLabeled(firstStatement);

        ModularPlusCalValidationPlusCalStatementVisitor visitor = new ModularPlusCalValidationPlusCalStatementVisitor(this.ctx);
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

            ModularPlusCalValidationPlusCalStatementVisitor visitor = new ModularPlusCalValidationPlusCalStatementVisitor(this.ctx);
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
            ctx.error(new InvalidModularPlusCalIssue(InvalidModularPlusCalIssue.InvalidReason.MISSING_LABEL, statement));
        }

        return null;
    }
}