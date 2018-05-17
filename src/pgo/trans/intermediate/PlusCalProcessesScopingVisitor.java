package pgo.trans.intermediate;

import pgo.model.pcal.MultiProcess;
import pgo.model.pcal.ProcessesVisitor;
import pgo.model.pcal.SingleProcess;

public class PlusCalProcessesScopingVisitor extends ProcessesVisitor<Void, RuntimeException> {

	PlusCalScopeBuilder builder;
	
	public PlusCalProcessesScopingVisitor(PlusCalScopeBuilder builder) {
		this.builder = builder;
	}
	
	@Override
	public Void visit(SingleProcess singleProcess) throws RuntimeException {
		
		return null;
	}

	@Override
	public Void visit(MultiProcess multiProcess) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

}
