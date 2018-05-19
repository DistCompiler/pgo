package pgo.formatters;

import java.io.IOException;

import pgo.errors.ContextVisitor;
import pgo.trans.intermediate.ExpandingMacroCall;
import pgo.trans.intermediate.WhileLoadingUnit;

public class ContextFormattingVisitor extends ContextVisitor<Void, IOException> {

	private IndentingWriter out;

	public ContextFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(WhileLoadingUnit whileLoadingUnit) throws IOException {
		out.write("while loading unit required from line ");
		out.write(whileLoadingUnit.getUnit().getLocation().getStartLine());
		out.write(" column ");
		out.write(whileLoadingUnit.getUnit().getLocation().getStartColumn());
		return null;
	}

	@Override
	public Void visit(ExpandingMacroCall expandingMacroCall) throws IOException {
		out.write("while expanding macro call at line ");
		out.write(expandingMacroCall.getMacroCall().getLocation().getStartLine());
		out.write(" column ");
		out.write(expandingMacroCall.getMacroCall().getLocation().getStartColumn());
		return null;
	}

}
