package pgo.trans.intermediate;

import pcal.AST;
import pgo.PGoException;
import pgo.errors.IssueContext;
import pgo.model.pcal.Algorithm;
import pgo.util.PcalASTUtil;
import pgo.util.TLCToPGoPCalASTConversionVisitor;

public class PlusCalConversionPass {
	
	private PlusCalConversionPass() {}
	
	public static Algorithm perform(IssueContext ctx, AST ast) {
		TLCToPGoPCalASTConversionVisitor v = new TLCToPGoPCalASTConversionVisitor(ctx);
		try {
			PcalASTUtil.accept(ast, v);
		} catch (PGoException e) {
			throw new RuntimeException("PlusCal AST conversion should not throw exceptions", e);
		}
		return v.getResult();
	}

}
