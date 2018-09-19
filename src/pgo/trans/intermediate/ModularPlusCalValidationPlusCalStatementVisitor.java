package pgo.trans.intermediate;

import pgo.TODO;
import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;

import java.util.List;

/**
 * Performs Modular PlusCal validation at the level of PlusCal statements.
 * Note that TLA+ expressions are not validated since they cannot contain
 * invalid semantics.
 */
public class ModularPlusCalValidationPlusCalStatementVisitor extends PlusCalStatementVisitor<Void, RuntimeException> {
    private IssueContext ctx;
    private PlusCalStatement previousStatement;

    public ModularPlusCalValidationPlusCalStatementVisitor(IssueContext ctx) {
        this.ctx = ctx;
        this.previousStatement = null;
    }

    public Void visit(PlusCalLabeledStatements labeledStatements) {
        this.previousStatement = labeledStatements;

        for (PlusCalStatement statement : labeledStatements.getStatements()) {
            statement.accept(this);
        }

        return null;
    }

    public Void visit(PlusCalWhile plusCalWhile) {
        // do not flag missing label if the 'while' statement has no previous statement
        // since that will already be flagged previously (the first statement of every
        // process/procedure/archetype needs to be labeled).
        if (previousStatement != null && !(previousStatement instanceof PlusCalLabeledStatements)) {
            missingLabel(plusCalWhile);
        }

        this.previousStatement = plusCalWhile;

        for (PlusCalStatement statement : plusCalWhile.getBody()) {
            statement.accept(this);
        }

        return null;
    }

    public Void visit(PlusCalIf plusCalIf) {
        this.previousStatement = plusCalIf;

        for (PlusCalStatement statement : plusCalIf.getYes()) {
            statement.accept(this);
        }

        for (PlusCalStatement statement : plusCalIf.getNo()) {
            statement.accept(this);
        }

        return null;
    }

    public Void visit(PlusCalEither plusCalEither) {
        this.previousStatement = plusCalEither;

        for (List<PlusCalStatement> cases : plusCalEither.getCases()) {
            for (PlusCalStatement statement : cases) {
                statement.accept(this);
            }
        }

        return null;
    }

    public Void visit(PlusCalAssignment plusCalAssignment) {
        throw new TODO();
    }

    public Void visit(PlusCalReturn plusCalReturn) {
        throw new TODO();
    }

    public Void visit(PlusCalSkip skip) {
        throw new TODO();
    }

    public Void visit(PlusCalCall plusCalCall) {
        throw new TODO();
    }

    public Void visit(PlusCalMacroCall macroCall) {
        throw new TODO();
    }

    public Void visit(PlusCalWith with) {
        throw new TODO();
    }

    public Void visit(PlusCalPrint plusCalPrint) {
        this.previousStatement = plusCalPrint;
        return null;
    }

    public Void visit(PlusCalAssert plusCalAssert) {
        throw new TODO();
    }

    public Void visit(PlusCalAwait plusCalAwait) {
        throw new TODO();
    }

    public Void visit(PlusCalGoto plusCalGoto) {
        throw new TODO();
    }

    public Void visit(ModularPlusCalYield modularPlusCalYield) {
        throw new TODO();
    }

    private void missingLabel(PlusCalStatement statement) {
        this.ctx.error(new InvalidModularPlusCalIssue(
                InvalidModularPlusCalIssue.InvalidReason.MISSING_LABEL,
                statement
        ));
    }
}
