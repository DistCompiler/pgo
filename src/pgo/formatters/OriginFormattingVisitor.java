package pgo.formatters;

import pgo.util.Derived;
import pgo.util.OriginVisitor;
import pgo.util.SourceLocatable;

import java.io.IOException;

public class OriginFormattingVisitor extends OriginVisitor<Void, IOException> {

	private final IndentingWriter out;

	public OriginFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(SourceLocatable sourceLocatable) throws IOException {
		out.write("source [");
		out.write(sourceLocatable.toString());		
		out.write("] at line ");
		out.write(Integer.toString(sourceLocatable.getLocation().getStartLine()));
		out.write(" column ");
		out.write(Integer.toString(sourceLocatable.getLocation().getStartColumn()));
		return null;
	}

	@Override
	public Void visit(Derived derived) throws IOException {
		derived.accept(new DerivedFormattingVisitor(out));
		return null;
	}

}
