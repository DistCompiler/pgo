package pgo.trans.intermediate;

import pgo.errors.Context;
import pgo.errors.ContextVisitor;
import pgo.model.pcal.MacroCall;

public class ExpandingMacroCall extends Context {

	private MacroCall macroCall;

	public ExpandingMacroCall(MacroCall macroCall) {
		this.macroCall = macroCall;
	}

	public MacroCall getMacroCall() {
		return macroCall;
	}

	@Override
	public <T, E extends Throwable> T accept(ContextVisitor<T, E> ctx) throws E {
		return ctx.visit(this);
	}

}
