package pgo.trans.passes.mpcal;

import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.trans.intermediate.ModularPlusCalValidationVisitor;

public class ModularPlusCalValidationPass {
    private ModularPlusCalValidationPass() {}

    public static Void perform(IssueContext ctx, ModularPlusCalBlock mpcal) {
        mpcal.accept(new ModularPlusCalValidationVisitor(ctx));
        return null;
    }
}
