package pgo.formatters;

import java.io.IOException;

import pgo.scope.UID;
import pgo.util.DerivedVisitor;
import pgo.util.Origin;

public class DerivedFormattingVisitor extends DerivedVisitor<Void, IOException> {

	private IndentingWriter out;

	public DerivedFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(UID uid) throws IOException {
		out.write("symbol derived from ");
		boolean first = true;
		try(IndentingWriter.Indent i_ = out.indent()){
			for(Origin o : uid.getOrigins()) {
				if(first) {
					first = false;
				}else {
					out.write(", ");
				}
				o.accept(new OriginFormattingVisitor(out));
			}
		}
		return null;
	}

}
