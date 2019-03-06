package pgo.trans.passes.validation;

import pgo.TODO;
import pgo.errors.IssueContext;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.tla.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.*;

public class ModularPlusCalTLAExpressionValidationVisitor extends TLAExpressionVisitor<Void, RuntimeException> {
    private final IssueContext ctx;
    private final DefinitionRegistry registry;
    private final PlusCalStatement containingStatement;
    private final Map<UID, Boolean> functionMapped;

    public ModularPlusCalTLAExpressionValidationVisitor(IssueContext ctx, DefinitionRegistry registry, PlusCalStatement containingStatement,
                                                        Map<UID, Boolean> functionMapped) {
        this.ctx = ctx;
        this.registry = registry;
        this.containingStatement = containingStatement;
        this.functionMapped = functionMapped;
    }

    @Override
    public Void visit(TLAFunctionCall tlaFunctionCall) throws RuntimeException {
        tlaFunctionCall.getParams().forEach(param -> param.accept(this));

        if (tlaFunctionCall.getFunction() instanceof TLAGeneralIdentifier) {
            UID varUID = registry.followReference(tlaFunctionCall.getFunction().getUID());

            if (functionMapped.containsKey(varUID) && !functionMapped.get(varUID)) {
                ctx.error(new InvalidArchetypeResourceUsageIssue(containingStatement, varUID, false));
            }
        }

        return null;
    }

    @Override
    public Void visit(TLABinOp tlaBinOp) throws RuntimeException {
        tlaBinOp.getLHS().accept(this);
        tlaBinOp.getRHS().accept(this);

        return null;
    }

    @Override
    public Void visit(TLABool tlaBool) throws RuntimeException {
        return null;
    }

    @Override
    public Void visit(TLACase tlaCase) throws RuntimeException {
        tlaCase.getArms().forEach(arm -> {
            arm.getCondition().accept(this);
            arm.getResult().accept(this);
        });

        return null;
    }

    @Override
    public Void visit(TLADot tlaDot) throws RuntimeException {
        tlaDot.getExpression().accept(this);

        return null;
    }

    @Override
    public Void visit(TLAExistential tlaExistential) throws RuntimeException {
        throw new TODO();
    }

    @Override
    public Void visit(TLAFunction tlaFunction) throws RuntimeException {
        tlaFunction.getBody().accept(this);

        return null;
    }

    @Override
    public Void visit(TLAFunctionSet tlaFunctionSet) throws RuntimeException {
        throw new TODO();
    }

    @Override
    public Void visit(TLAFunctionSubstitution tlaFunctionSubstitution) throws RuntimeException {
        throw new TODO();
    }

    @Override
    public Void visit(TLAIf tlaIf) throws RuntimeException {
        tlaIf.getCond().accept(this);
        tlaIf.getTval().accept(this);
        tlaIf.getFval().accept(this);

        return null;
    }

    @Override
    public Void visit(TLALet tlaLet) throws RuntimeException {
        throw new TODO();
    }

    @Override
    public Void visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
        UID varUID = registry.followReference(tlaGeneralIdentifier.getUID());

        if (functionMapped.containsKey(varUID) && functionMapped.get(varUID)) {
            ctx.error(new InvalidArchetypeResourceUsageIssue(containingStatement, varUID, true));
        }

        return null;
    }

    @Override
    public Void visit(TLATuple tlaTuple) throws RuntimeException {
        tlaTuple.getElements().forEach(e -> e.accept(this));

        return null;
    }

    @Override
    public Void visit(TLAMaybeAction tlaMaybeAction) throws RuntimeException {
        throw new TODO();
    }

    @Override
    public Void visit(TLANumber tlaNumber) throws RuntimeException {
        return null;
    }

    @Override
    public Void visit(TLAOperatorCall tlaOperatorCall) throws RuntimeException {
        tlaOperatorCall.getArgs().forEach(arg -> arg.accept(this));

        return null;
    }

    @Override
    public Void visit(TLAQuantifiedExistential tlaQuantifiedExistential) throws RuntimeException {
        tlaQuantifiedExistential.getBody().accept(this);

        return null;
    }

    @Override
    public Void visit(TLAQuantifiedUniversal tlaQuantifiedUniversal) throws RuntimeException {
        tlaQuantifiedUniversal.getBody().accept(this);

        return null;
    }

    @Override
    public Void visit(TLARecordConstructor tlaRecordConstructor) throws RuntimeException {
        tlaRecordConstructor.getFields().forEach(field -> field.getValue().accept(this));

        return null;
    }

    @Override
    public Void visit(TLARecordSet tlaRecordSet) throws RuntimeException {
        throw new TODO();
    }

    @Override
    public Void visit(TLARequiredAction tlaRequiredAction) throws RuntimeException {
        throw new TODO();
    }

    @Override
    public Void visit(TLASetConstructor tlaSetConstructor) throws RuntimeException {
        tlaSetConstructor.getContents().forEach(e -> e.accept(this));

        return null;
    }

    @Override
    public Void visit(TLASetComprehension tlaSetComprehension) throws RuntimeException {
        tlaSetComprehension.getBody().accept(this);

        return null;
    }

    @Override
    public Void visit(TLASetRefinement tlaSetRefinement) throws RuntimeException {
        tlaSetRefinement.getFrom().accept(this);
        tlaSetRefinement.getWhen().accept(this);

        return null;
    }

    @Override
    public Void visit(TLAString tlaString) throws RuntimeException {
        return null;
    }

    @Override
    public Void visit(TLAUnary tlaUnary) throws RuntimeException {
        tlaUnary.getOperand().accept(this);

        return null;
    }

    @Override
    public Void visit(TLAUniversal tlaUniversal) throws RuntimeException {
        throw new TODO();
    }

    @Override
    public Void visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
        return null;
    }

    @Override
    public Void visit(TLAFairness fairness) throws RuntimeException {
        throw new TODO();
    }

    @Override
    public Void visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
        throw new TODO();
    }

    @Override
    public Void visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
        throw new TODO();
    }

    @Override
    public Void visit(TLARef tlaRef) throws RuntimeException {
        return null;
    }
}