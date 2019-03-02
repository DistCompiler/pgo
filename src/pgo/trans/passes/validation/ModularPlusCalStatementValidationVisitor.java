package pgo.trans.passes.validation;

import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.*;
import java.util.stream.IntStream;

public class ModularPlusCalStatementValidationVisitor extends PlusCalStatementVisitor<Void, RuntimeException> {
    private IssueContext ctx;
    private Map<String, Boolean> functionMapped;

    public ModularPlusCalStatementValidationVisitor(IssueContext ctx, Map<String, Boolean> functionMapped) {
        this.ctx = ctx;
        this.functionMapped = functionMapped;
    }

    public Void visit(PlusCalLabeledStatements plusCalLabeledStatements) {
        plusCalLabeledStatements.getStatements().forEach(statement ->
            statement.accept(this)
        );

        return null;
    }

    public Void visit(PlusCalWhile plusCalWhile) {
        plusCalWhile.getCondition().accept(new ModularPlusCalTLAExpressionValidationVisitor(ctx, plusCalWhile, functionMapped));
        plusCalWhile.getBody().forEach(statement -> statement.accept(this));

        return null;
    }

    public Void visit(PlusCalIf plusCalIf) {
        plusCalIf.getCondition().accept(new ModularPlusCalTLAExpressionValidationVisitor(ctx, plusCalIf, functionMapped));
        plusCalIf.getYes().forEach(statement -> statement.accept(this));
        plusCalIf.getNo().forEach(statement -> statement.accept(this));

        return null;
    }

    public Void visit(PlusCalEither plusCalEither) {
        plusCalEither.getCases().forEach(aCase ->
            aCase.forEach(statement -> statement.accept(this))
        );

        return null;
    }

    public Void visit(PlusCalAssignment plusCalAssignment) {
        plusCalAssignment.getPairs().forEach(pair -> {
            pair.getLhs().accept(new ModularPlusCalTLAExpressionValidationVisitor(ctx, plusCalAssignment, functionMapped));
            pair.getRhs().accept(new ModularPlusCalTLAExpressionValidationVisitor(ctx, plusCalAssignment, functionMapped));
        });

        return null;
    }

    public Void visit(PlusCalReturn plusCalReturn) {
        return null;
    }

    public Void visit(PlusCalSkip plusCalSkip) {
        return null;
    }

    public Void visit(PlusCalCall plusCalCall) {
        plusCalCall.getArguments().forEach(arg ->
                arg.accept(new ModularPlusCalTLAExpressionValidationVisitor(ctx, plusCalCall, functionMapped))
        );

        return null;
    }

    public Void visit(PlusCalMacroCall macroCall) {
        macroCall.getArguments().forEach(arg ->
                arg.accept(new ModularPlusCalTLAExpressionValidationVisitor(ctx, macroCall, functionMapped))
        );

        return null;
    }

    public Void visit(PlusCalWith plusCalWith) {
        plusCalWith.getVariables().forEach(varDecl ->
                varDecl.getValue().accept(new ModularPlusCalTLAExpressionValidationVisitor(ctx, plusCalWith, functionMapped))
        );
        plusCalWith.getBody().forEach(statement -> statement.accept(this));

        return null;
    }

    public Void visit(PlusCalPrint plusCalPrint) {
        plusCalPrint.getValue().accept(new ModularPlusCalTLAExpressionValidationVisitor(ctx, plusCalPrint, functionMapped));

        return null;
    }

    public Void visit(PlusCalAssert plusCalAssert) {
        plusCalAssert.getCondition().accept(new ModularPlusCalTLAExpressionValidationVisitor(ctx, plusCalAssert, functionMapped));

        return null;
    }

    public Void visit(PlusCalAwait plusCalAwait) {
        plusCalAwait.getCondition().accept(new ModularPlusCalTLAExpressionValidationVisitor(ctx, plusCalAwait, functionMapped));

        return null;
    }

    public Void visit(PlusCalGoto plusCalGoto) {
        return null;
    }

    public Void visit(ModularPlusCalYield modularPlusCalYield) {
        throw new Unreachable();
    }
}