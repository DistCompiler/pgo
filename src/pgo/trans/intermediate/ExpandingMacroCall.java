package pgo.trans.intermediate;

import pgo.errors.Context;
import pgo.errors.ContextVisitor;
import pgo.model.pcal.PlusCalMacroCall;

public class ExpandingMacroCall extends Context {

	private PlusCalMacroCall macroCall;

	public ExpandingMacroCall(PlusCalMacroCall macroCall) {
		this.macroCall = macroCall;
	}

	public PlusCalMacroCall getMacroCall() {
		return macroCall;
	}

	@Override
	public <T, E extends Throwable> T accept(ContextVisitor<T, E> ctx) throws E {
		return ctx.visit(this);
	}

}
