package pgo.trans.intermediate;

import pgo.PGoOptions;
import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.PlusCalAlgorithm;
import pgo.model.pcal.PlusCalMultiProcess;
import pgo.model.pcal.PlusCalProcessesVisitor;
import pgo.model.pcal.PlusCalSingleProcess;

public class CheckOptionsPass {
	
	private CheckOptionsPass() {}
	
	public static void perform(IssueContext ctx, ModularPlusCalBlock modularPlusCalBlock, PGoOptions options) {
		modularPlusCalBlock.getProcesses().accept(new PlusCalProcessesVisitor<Void, RuntimeException>() {

			@Override
			public Void visit(PlusCalSingleProcess singleProcess) throws RuntimeException {
				if (options.net.isEnabled()) {
					ctx.error(new UnsupportedFeatureIssue("networked single process"));
				}
				if (!modularPlusCalBlock.getInstances().isEmpty()) {
					ctx.error(new UnsupportedFeatureIssue("single process with instances"));
				}
				return null;
			}

			@Override
			public Void visit(PlusCalMultiProcess multiProcess) throws RuntimeException {
				// pass
				return null;
			}
			
		});
	}

}
