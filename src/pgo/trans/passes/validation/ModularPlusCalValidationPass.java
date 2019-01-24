package pgo.trans.passes.validation;

import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalBlock;

public class ModularPlusCalValidationPass {
    private ModularPlusCalValidationPass() {}

    public static Void perform(IssueContext ctx, ModularPlusCalBlock mpcal) {
        mpcal.accept(new ModularPlusCalValidationVisitor(ctx));
        return null;
    }
}
