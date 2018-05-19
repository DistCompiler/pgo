package pgo.formatters;

import java.io.IOException;

import pgo.parser.ActionContextVisitor;
import pgo.parser.AfterParsingUnit;
import pgo.parser.WhileParsingBuiltinToken;

public class ParseActionContextFormattingVisitor extends ActionContextVisitor<Void, IOException> {

	private IndentingWriter out;

	public ParseActionContextFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}
	
	@Override
	public Void visit(WhileParsingBuiltinToken whileParsingBuiltinToken) throws IOException {
		out.write("while parsing builtin token \"");
		out.write(whileParsingBuiltinToken.getToken());
		out.write("\"");
		return null;
	}

	@Override
	public Void visit(AfterParsingUnit afterParsingUnit) throws IOException {
		if(afterParsingUnit.getLastUnit() == null) {
			out.write("after parsing no units");
		}else {
			out.write("after parsing unit:");
			out.newLine();
			try(IndentingWriter.Indent i_ = out.indent()){
				afterParsingUnit.getLastUnit().accept(new PGoTLAUnitFormattingVisitor(out));
			}
		}
		return null;
	}

}
