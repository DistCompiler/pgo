package pgo.trans.intermediate;

import pgo.TODO;
import pgo.Unreachable;
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
        if (!firstOrLabeled(previousStatement)) {
            missingLabel(plusCalWhile);
        }

        this.previousStatement = plusCalWhile;

        for (PlusCalStatement statement : plusCalWhile.getBody()) {
            statement.accept(this);
        }

        return null;
    }

    public Void visit(PlusCalIf plusCalIf) {
        checkProcedureCall(plusCalIf);
        checkReturnOrGoto(plusCalIf);
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
        checkProcedureCall(plusCalEither);
        checkReturnOrGoto(plusCalEither);
        this.previousStatement = plusCalEither;

        for (List<PlusCalStatement> cases : plusCalEither.getCases()) {
            for (PlusCalStatement statement : cases) {
                statement.accept(this);
            }
        }

        return null;
    }

    public Void visit(PlusCalAssignment plusCalAssignment) {
        checkProcedureCall(plusCalAssignment);
        checkReturnOrGoto(plusCalAssignment);
        this.previousStatement = plusCalAssignment;

        return null;
    }

    public Void visit(PlusCalReturn plusCalReturn) {
        // `return` statements can follow procedure calls -- no checks here
        checkReturnOrGoto(plusCalReturn);

        this.previousStatement = plusCalReturn;
        return null;
    }

    public Void visit(PlusCalSkip skip) {
        checkProcedureCall(skip);
        checkReturnOrGoto(skip);
        this.previousStatement = skip;

        return null;
    }

    public Void visit(PlusCalCall plusCalCall) {
        checkProcedureCall(plusCalCall);
        checkReturnOrGoto(plusCalCall);
        this.previousStatement = plusCalCall;

        return null;
    }

    public Void visit(PlusCalMacroCall macroCall) {
        checkProcedureCall(macroCall);
        checkReturnOrGoto(macroCall);
        this.previousStatement = macroCall;
        return null;
    }

    public Void visit(PlusCalWith with) {
        checkProcedureCall(with);
        checkReturnOrGoto(with);
        this.previousStatement = with;

        return null;
    }

    public Void visit(PlusCalPrint plusCalPrint) {
        checkProcedureCall(plusCalPrint);
        checkReturnOrGoto(plusCalPrint);
        this.previousStatement = plusCalPrint;

        return null;
    }

    public Void visit(PlusCalAssert plusCalAssert) {
        checkProcedureCall(plusCalAssert);
        checkReturnOrGoto(plusCalAssert);
        this.previousStatement = plusCalAssert;

        return null;
    }

    public Void visit(PlusCalAwait plusCalAwait) {
        checkProcedureCall(plusCalAwait);
        checkReturnOrGoto(plusCalAwait);
        this.previousStatement = plusCalAwait;

        return null;
    }

    public Void visit(PlusCalGoto plusCalGoto) {
        // `goto` statements can follow procedure calls -- no checks here
        checkReturnOrGoto(plusCalGoto);
        this.previousStatement = plusCalGoto;

        return null;
    }

    public Void visit(ModularPlusCalYield modularPlusCalYield) {
        throw new Unreachable();
    }

    private void missingLabel(PlusCalStatement statement) {
        this.ctx.error(new InvalidModularPlusCalIssue(
                InvalidModularPlusCalIssue.InvalidReason.MISSING_LABEL,
                statement
        ));
    }


    // checks whether the statement given is the first of an archetype/procedure/process,
    // or if it is a labeled statement. The label checks in this visitor do not flag
    // the case when the first statement is not labeled since that is already taken care
    // of by ModularPlusCalValidationVisitor.
    private boolean firstOrLabeled(PlusCalStatement statement) {
        return (statement == null) || (statement instanceof PlusCalLabeledStatements);
    }

    private void checkProcedureCall(PlusCalStatement statement) {
        if (previousStatement instanceof PlusCalCall) {
            missingLabel(statement);
        }
    }

    private void checkReturnOrGoto(PlusCalStatement statement) {
        if ((previousStatement instanceof PlusCalReturn) || (previousStatement instanceof PlusCalGoto)) {
            missingLabel(statement);
        }
    }
}
