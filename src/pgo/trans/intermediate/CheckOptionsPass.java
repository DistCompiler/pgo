package pgo.trans.intermediate;

import pgo.PGoOptions;
import pgo.errors.IssueContext;
import pgo.model.pcal.Algorithm;
import pgo.model.pcal.MultiProcess;
import pgo.model.pcal.ProcessesVisitor;
import pgo.model.pcal.SingleProcess;

public class CheckOptionsPass {
	
	private CheckOptionsPass() {}
	
	public static void perform(IssueContext ctx, Algorithm algorithm, PGoOptions options) {
		algorithm.getProcesses().accept(new ProcessesVisitor<Void, RuntimeException>() {

			@Override
			public Void visit(SingleProcess singleProcess) throws RuntimeException {
				if(options.net.isEnabled()) {
					ctx.error(new UnsupportedFeatureIssue("networked single-process algorithm"));
				}
				return null;
			}

			@Override
			public Void visit(MultiProcess multiProcess) throws RuntimeException {
				// pass
				return null;
			}
			
		});
	}

}
