package pgo.trans.passes.expansion;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.pcal.PlusCalMacro;
import pgo.model.pcal.PlusCalMacroCall;

public class MacroArgumentCountMismatchIssue extends Issue {

	private final PlusCalMacroCall macroCall;
	private final PlusCalMacro macro;

	public MacroArgumentCountMismatchIssue(PlusCalMacroCall macroCall, PlusCalMacro macro) {
		this.macroCall = macroCall;
		this.macro = macro;
	}

	public PlusCalMacroCall getMacroCall() {
		return macroCall;
	}

	public PlusCalMacro getMacro() {
		return macro;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
