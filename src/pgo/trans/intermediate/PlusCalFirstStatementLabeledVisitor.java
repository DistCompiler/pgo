package pgo.trans.intermediate;

import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;

/**
 * Validates that the first statement starting at a particular node is labeled. Used to verify
 * that Modular PlusCal specs obey the PlusCal rule which states that the first statement of
 * a procedure, process or archetype needs to be labeled.
 */
public class PlusCalFirstStatementLabeledVisitor extends PlusCalStatementVisitor<Boolean, RuntimeException> {

    public Boolean visit(PlusCalLabeledStatements plusCalLabeledStatements) {
        return true;
    }

    public Boolean visit(PlusCalWhile plusCalWhile) {
        return false;
    }

    public Boolean visit(PlusCalIf plusCalIf) {
        return false;
    }

    public Boolean visit(PlusCalEither plusCalEither) {
        return false;
    }

    public Boolean visit(PlusCalAssignment plusCalAssignment) {
        return false;
    }

    public Boolean visit(PlusCalReturn plusCalReturn) {
        return false;
    }

    public Boolean visit(PlusCalSkip plusCalSkip) {
        return false;
    }

    public Boolean visit(PlusCalCall plusCalCall) {
        return false;
    }

    public Boolean visit(PlusCalMacroCall macroCall) {
        return false;
    }

    public Boolean visit(PlusCalWith plusCalWith) {
        return false;
    }

    public Boolean visit(PlusCalPrint plusCalPrint) {
        return false;
    }

    public Boolean visit(PlusCalAssert plusCalAssert) {
        return false;
    }
    public Boolean visit(PlusCalAwait plusCalAwait) {
        return false;
    }

    public Boolean visit(PlusCalGoto plusCalGoto) {
        return false;
    }

    public Boolean visit(ModularPlusCalYield modularPlusCalYield) {
        return false;
    }
}
