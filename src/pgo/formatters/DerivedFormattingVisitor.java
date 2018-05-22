package pgo.formatters;

import java.io.IOException;

import pgo.model.type.PGoType;
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
		out.write("derived from ");
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

	@Override
	public Void visit(PGoType pGoType) throws IOException {
		out.write("type derived from ");
		boolean first = true;
		try(IndentingWriter.Indent i_ = out.indent()){
			for(Origin o : pGoType.getOrigins()) {
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
