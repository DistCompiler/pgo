package pgo.formatters;

import java.io.IOException;

import pgo.model.type.PGoType;
import pgo.scope.UID;
import pgo.trans.intermediate.OperatorAccessor;
import pgo.util.Derived;
import pgo.util.DerivedVisitor;
import pgo.util.Origin;

public class DerivedFormattingVisitor extends DerivedVisitor<Void, IOException> {

	private IndentingWriter out;

	public DerivedFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}
	
	private void writeOrigins(Derived d) throws IOException {
		boolean first = true;
		try(IndentingWriter.Indent i_ = out.indent()){
			for(Origin o : d.getOrigins()) {
				if(first) {
					first = false;
				}else {
					out.write(", ");
				}
				o.accept(new OriginFormattingVisitor(out));
			}
		}
	}

	@Override
	public Void visit(UID uid) throws IOException {
		out.write("derived from ");
		writeOrigins(uid);
		return null;
	}

	@Override
	public Void visit(PGoType pGoType) throws IOException {
		out.write("type derived from ");
		writeOrigins(pGoType);
		return null;
	}

	@Override
	public Void visit(OperatorAccessor operatorAccessor) throws IOException {
		out.write("TLA operator derived from ");
		writeOrigins(operatorAccessor);
		return null;
	}

}
