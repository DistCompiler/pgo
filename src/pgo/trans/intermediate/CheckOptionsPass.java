package pgo.trans.intermediate;

import pgo.PGoOptions;
import pgo.errors.IssueContext;
import pgo.model.pcal.PlusCalAlgorithm;
import pgo.model.pcal.PlusCalMultiProcess;
import pgo.model.pcal.PlusCalProcessesVisitor;
import pgo.model.pcal.PlusCalSingleProcess;

public class CheckOptionsPass {
	
	private CheckOptionsPass() {}
	
	public static void perform(IssueContext ctx, PlusCalAlgorithm plusCalAlgorithm, PGoOptions options) {
		plusCalAlgorithm.getProcesses().accept(new PlusCalProcessesVisitor<Void, RuntimeException>() {

			@Override
			public Void visit(PlusCalSingleProcess singleProcess) throws RuntimeException {
				if(options.net.isEnabled()) {
					ctx.error(new UnsupportedFeatureIssue("networked single-process plusCalAlgorithm"));
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
