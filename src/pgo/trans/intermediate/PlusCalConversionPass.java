package pgo.trans.intermediate;

import pgo.PGoException;
import pgo.errors.IssueContext;
import pgo.model.pcal.Algorithm;
import pgo.parser.PcalParser.ParsedPcal;
import pgo.util.PcalASTUtil;
import pgo.util.TLCToPGoPCalASTConversionVisitor;

public class PlusCalConversionPass {
	
	private PlusCalConversionPass() {}
	
	public static Algorithm perform(IssueContext ctx, ParsedPcal pcal) {
		TLCToPGoPCalASTConversionVisitor v = new TLCToPGoPCalASTConversionVisitor(ctx);
		try {
			PcalASTUtil.accept(pcal.getAST(), v);
		} catch (PGoException e) {
			throw new RuntimeException("PlusCal AST conversion should not throw exceptions", e);
		}
		return v.getResult();
	}

}
