package pgo.errors;

import pgo.trans.passes.expansion.ExpandingMacroCall;
import pgo.trans.intermediate.WhileLoadingUnit;

public abstract class ContextVisitor<T, E extends Throwable> {

	public abstract T visit(WhileLoadingUnit whileLoadingUnit) throws E;
	public abstract T visit(ExpandingMacroCall expandingMacroCall) throws E;

}
