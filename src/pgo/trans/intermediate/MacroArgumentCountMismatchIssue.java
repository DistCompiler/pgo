package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.pcal.Macro;
import pgo.model.pcal.MacroCall;

public class MacroArgumentCountMismatchIssue extends Issue {

	private MacroCall macroCall;
	private Macro macro;

	public MacroArgumentCountMismatchIssue(MacroCall macroCall, Macro macro) {
		this.macroCall = macroCall;
		this.macro = macro;
	}

	public MacroCall getMacroCall() {
		return macroCall;
	}

	public Macro getMacro() {
		return macro;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
