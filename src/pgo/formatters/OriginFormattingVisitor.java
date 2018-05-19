package pgo.formatters;

import java.io.IOException;

import pgo.util.Derived;
import pgo.util.OriginVisitor;
import pgo.util.SourceLocatable;

public class OriginFormattingVisitor extends OriginVisitor<Void, IOException> {

	private IndentingWriter out;

	public OriginFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(SourceLocatable sourceLocatable) throws IOException {
		out.write("source at line ");
		out.write(sourceLocatable.getLocation().getStartLine());
		out.write(" column ");
		out.write(sourceLocatable.getLocation().getStartColumn());
		return null;
	}

	@Override
	public Void visit(Derived derived) throws IOException {
		derived.accept(new DerivedFormattingVisitor(out));
		return null;
	}

}
