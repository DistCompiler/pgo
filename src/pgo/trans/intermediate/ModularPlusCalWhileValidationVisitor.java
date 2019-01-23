package pgo.trans.intermediate;

import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;

import java.util.List;

/**
 * Validates that a `while` loop is not followed by other PlusCal processes in the same label.
 * This restriction is due to the way we desugar loops (`if` condition + `goto` statement), coupled
 * to the fact that we need to be able to insert assignments to temporary bindings when expanding
 * mapping macros.
 */
public class ModularPlusCalWhileValidationVisitor extends PlusCalStatementVisitor<Void, RuntimeException> {
    IssueContext ctx;

    public ModularPlusCalWhileValidationVisitor(IssueContext ctx) {
        this.ctx = ctx;
    }

    @Override
    public Void visit(PlusCalLabeledStatements plusCalLabeledStatements) throws RuntimeException {
        for(PlusCalStatement stmt : plusCalLabeledStatements.getStatements()) {
            stmt.accept(this);
        }

        List<PlusCalStatement> statements = plusCalLabeledStatements.getStatements();
        if (statements.size() > 1 && statements.get(0) instanceof PlusCalWhile) {
            PlusCalStatement invalidStatement = statements.get(1);
            ctx.error(new StatementNotAllowedIssue(invalidStatement));
        }

        return null;
    }

    @Override
    public Void visit(PlusCalWhile plusCalWhile) throws RuntimeException {
        for(PlusCalStatement stmt : plusCalWhile.getBody()) {
            stmt.accept(this);
        }
        return null;
    }

    @Override
    public Void visit(PlusCalIf plusCalIf) throws RuntimeException {
        for(PlusCalStatement stmt : plusCalIf.getYes()) {
            stmt.accept(this);
        }
        for(PlusCalStatement stmt : plusCalIf.getNo()) {
            stmt.accept(this);
        }
        return null;
    }

    @Override
    public Void visit(PlusCalEither plusCalEither) throws RuntimeException {
        for(List<PlusCalStatement> list : plusCalEither.getCases()) {
            for(PlusCalStatement stmt : list) {
                stmt.accept(this);
            }
        }
        return null;
    }

    @Override
    public Void visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
        return null;
    }

    @Override
    public Void visit(PlusCalReturn plusCalReturn) throws RuntimeException {
        return null;
    }

    @Override
    public Void visit(PlusCalSkip plusCalSkip) throws RuntimeException {
        return null;
    }

    @Override
    public Void visit(PlusCalCall plusCalCall) throws RuntimeException {
        return null;
    }

    @Override
    public Void visit(PlusCalMacroCall macroCall) throws RuntimeException {
        throw new Unreachable();
    }

    @Override
    public Void visit(PlusCalWith plusCalWith) throws RuntimeException {
        for(PlusCalStatement stmt : plusCalWith.getBody()) {
            stmt.accept(this);
        }
        return null;
    }

    @Override
    public Void visit(PlusCalPrint plusCalPrint) throws RuntimeException {
        return null;
    }

    @Override
    public Void visit(PlusCalAssert plusCalAssert) throws RuntimeException {
        return null;
    }

    @Override
    public Void visit(PlusCalAwait plusCalAwait) throws RuntimeException {
        return null;
    }

    @Override
    public Void visit(PlusCalGoto plusCalGoto) throws RuntimeException {
        return null;
    }

    @Override
    public Void visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
        return null;
    }
}
