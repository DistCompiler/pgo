package pgo.trans.passes.validation;

import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;

import java.util.List;

public class PlusCalStatementRejectionVisitor extends PlusCalStatementVisitor<Void, RuntimeException> {
    enum Node {
        LABELS, WHILE, IF, EITHER, ASSIGNMENT, RETURN, SKIP, CALL,
        MACRO_CALL, WITH, PRINT, ASSERT, AWAIT, GOTO, YIELD
    }

    IssueContext ctx;
    List<Node> rejections;

    public PlusCalStatementRejectionVisitor(IssueContext ctx, List<Node> rejections) {
        this.ctx = ctx;
        this.rejections = rejections;
    }

    @Override
    public Void visit(PlusCalLabeledStatements plusCalLabeledStatements) throws RuntimeException {
        if (this.rejections.contains(Node.LABELS)) {
            ctx.error(new StatementNotAllowedIssue(plusCalLabeledStatements));
        }

        for(PlusCalStatement stmt : plusCalLabeledStatements.getStatements()) {
            stmt.accept(this);
        }

        return null;
    }

    @Override
    public Void visit(PlusCalWhile plusCalWhile) throws RuntimeException {
        if (this.rejections.contains(Node.WHILE)) {
            ctx.error(new StatementNotAllowedIssue(plusCalWhile));
        }

        for(PlusCalStatement stmt : plusCalWhile.getBody()) {
            stmt.accept(this);
        }
        return null;
    }

    @Override
    public Void visit(PlusCalIf plusCalIf) throws RuntimeException {
        if (this.rejections.contains(Node.IF)) {
            ctx.error(new StatementNotAllowedIssue(plusCalIf));
        }

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
        if (this.rejections.contains(Node.EITHER)) {
            ctx.error(new StatementNotAllowedIssue(plusCalEither));
        }

        for(List<PlusCalStatement> list : plusCalEither.getCases()) {
            for(PlusCalStatement stmt : list) {
                stmt.accept(this);
            }
        }
        return null;
    }

    @Override
    public Void visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
        if (this.rejections.contains(Node.ASSIGNMENT)) {
            ctx.error(new StatementNotAllowedIssue(plusCalAssignment));
        }

        return null;
    }

    @Override
    public Void visit(PlusCalReturn plusCalReturn) throws RuntimeException {
        if (this.rejections.contains(Node.RETURN)) {
            ctx.error(new StatementNotAllowedIssue(plusCalReturn));
        }

        return null;
    }

    @Override
    public Void visit(PlusCalSkip plusCalSkip) throws RuntimeException {
        if (this.rejections.contains(Node.SKIP)) {
            ctx.error(new StatementNotAllowedIssue(plusCalSkip));
        }

        return null;
    }

    @Override
    public Void visit(PlusCalCall plusCalCall) throws RuntimeException {
        if (this.rejections.contains(Node.CALL)) {
            ctx.error(new StatementNotAllowedIssue(plusCalCall));
        }

        return null;
    }

    @Override
    public Void visit(PlusCalMacroCall macroCall) throws RuntimeException {
        if (this.rejections.contains(Node.MACRO_CALL)) {
            ctx.error(new StatementNotAllowedIssue(macroCall));
        }

        throw new Unreachable();
    }

    @Override
    public Void visit(PlusCalWith plusCalWith) throws RuntimeException {
        if (this.rejections.contains(Node.WITH)) {
            ctx.error(new StatementNotAllowedIssue(plusCalWith));
        }

        for(PlusCalStatement stmt : plusCalWith.getBody()) {
            stmt.accept(this);
        }
        return null;
    }

    @Override
    public Void visit(PlusCalPrint plusCalPrint) throws RuntimeException {
        if (this.rejections.contains(Node.PRINT)) {
            ctx.error(new StatementNotAllowedIssue(plusCalPrint));
        }

        return null;
    }

    @Override
    public Void visit(PlusCalAssert plusCalAssert) throws RuntimeException {
        if (this.rejections.contains(Node.ASSERT)) {
            ctx.error(new StatementNotAllowedIssue(plusCalAssert));
        }

        return null;
    }

    @Override
    public Void visit(PlusCalAwait plusCalAwait) throws RuntimeException {
        if (this.rejections.contains(Node.AWAIT)) {
            ctx.error(new StatementNotAllowedIssue(plusCalAwait));
        }

        return null;
    }

    @Override
    public Void visit(PlusCalGoto plusCalGoto) throws RuntimeException {
        if (this.rejections.contains(Node.GOTO)) {
            ctx.error(new StatementNotAllowedIssue(plusCalGoto));
        }

        return null;
    }

    @Override
    public Void visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
        if (this.rejections.contains(Node.YIELD)) {
            ctx.error(new StatementNotAllowedIssue(modularPlusCalYield));
        }

        return null;
    }
}
