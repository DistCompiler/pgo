package pgo.formatters;

import pgo.errors.ContextVisitor;
import pgo.trans.intermediate.ExpandingMacroCall;
import pgo.trans.intermediate.WhileLoadingUnit;

import java.io.IOException;

public class ContextFormattingVisitor extends ContextVisitor<Void, IOException> {

	private IndentingWriter out;

	public ContextFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(WhileLoadingUnit whileLoadingUnit) throws IOException {
		out.write("while loading unit required from line ");
		out.write(Integer.toString(whileLoadingUnit.getUnit().getLocation().getStartLine()));
		out.write(" column ");
		out.write(Integer.toString(whileLoadingUnit.getUnit().getLocation().getStartColumn()));
		return null;
	}

	@Override
	public Void visit(ExpandingMacroCall expandingMacroCall) throws IOException {
		out.write("while expanding macro call at line ");
		out.write(Integer.toString(expandingMacroCall.getMacroCall().getLocation().getStartLine()));
		out.write(" column ");
		out.write(Integer.toString(expandingMacroCall.getMacroCall().getLocation().getStartColumn()));
		return null;
	}

}
