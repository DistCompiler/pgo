package pgo.trans.passes.validation;

import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.*;

public class ModularPlusCalStatementValidationVisitor extends PlusCalStatementVisitor<Void, RuntimeException> {
    private final IssueContext ctx;
    private final DefinitionRegistry registry;
    private final Map<UID, Boolean> functionMapped;

    public ModularPlusCalStatementValidationVisitor(IssueContext ctx, DefinitionRegistry registry,
                                                    Map<UID, Boolean> functionMapped) {
        this.ctx = ctx;
        this.registry = registry;
        this.functionMapped = functionMapped;
    }

    public Void visit(PlusCalLabeledStatements plusCalLabeledStatements) {
        plusCalLabeledStatements.getStatements().forEach(statement ->
            statement.accept(this)
        );

        return null;
    }

    public Void visit(PlusCalWhile plusCalWhile) {
        plusCalWhile.getCondition().accept(new ModularPlusCalTLAExpressionValidationVisitor(
                ctx, registry, plusCalWhile, functionMapped));
        plusCalWhile.getBody().forEach(statement -> statement.accept(this));

        return null;
    }

    public Void visit(PlusCalIf plusCalIf) {
        plusCalIf.getCondition().accept(new ModularPlusCalTLAExpressionValidationVisitor(
                ctx, registry, plusCalIf, functionMapped));
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
            pair.getLhs().accept(
                    new ModularPlusCalTLAExpressionValidationVisitor(ctx, registry, plusCalAssignment, functionMapped));
            pair.getRhs().accept(
                    new ModularPlusCalTLAExpressionValidationVisitor(ctx, registry, plusCalAssignment, functionMapped));
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
                arg.accept(
                        new ModularPlusCalTLAExpressionValidationVisitor(ctx, registry, plusCalCall, functionMapped)));

        return null;
    }

    public Void visit(PlusCalMacroCall macroCall) {
        macroCall.getArguments().forEach(arg ->
                arg.accept(new ModularPlusCalTLAExpressionValidationVisitor(ctx, registry, macroCall, functionMapped)));

        return null;
    }

    public Void visit(PlusCalWith plusCalWith) {
        plusCalWith.getVariables().forEach(varDecl ->
                varDecl.getValue().accept(
                        new ModularPlusCalTLAExpressionValidationVisitor(ctx, registry, plusCalWith, functionMapped)));
        plusCalWith.getBody().forEach(statement -> statement.accept(this));

        return null;
    }

    public Void visit(PlusCalPrint plusCalPrint) {
        plusCalPrint.getValue().accept(
                new ModularPlusCalTLAExpressionValidationVisitor(ctx, registry, plusCalPrint, functionMapped));

        return null;
    }

    public Void visit(PlusCalAssert plusCalAssert) {
        plusCalAssert.getCondition().accept(
                new ModularPlusCalTLAExpressionValidationVisitor(ctx, registry, plusCalAssert, functionMapped));

        return null;
    }

    public Void visit(PlusCalAwait plusCalAwait) {
        plusCalAwait.getCondition().accept(
                new ModularPlusCalTLAExpressionValidationVisitor(ctx, registry, plusCalAwait, functionMapped));

        return null;
    }

    public Void visit(PlusCalGoto plusCalGoto) {
        return null;
    }

    public Void visit(ModularPlusCalYield modularPlusCalYield) {
        throw new Unreachable();
    }
}