package pgo.trans.intermediate;

import pgo.errors.Context;
import pgo.errors.ContextVisitor;
import pgo.util.SourceLocatable;

public class WhileLoadingUnit extends Context {

	SourceLocatable unit;
	
	public WhileLoadingUnit(SourceLocatable unit) {
		this.unit = unit;
	}
	
	public SourceLocatable getUnit() {
		return unit;
	}
	
	@Override
	public <T, E extends Throwable> T accept(ContextVisitor<T, E> ctx) throws E {
		return ctx.visit(this);
	}

}
