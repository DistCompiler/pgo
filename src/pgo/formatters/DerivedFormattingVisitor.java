package pgo.formatters;

import java.io.IOException;

import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeMonomorphicConstraint;
import pgo.model.type.PGoTypePolymorphicConstraint;
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
		if (d.getOrigins().isEmpty()) {
			out.write(" derived from ???");
		} else {
			out.write(" derived from ");
			boolean first = true;
			try (IndentingWriter.Indent ignored = out.indent()){
				for (Origin o : d.getOrigins()) {
					if (first) {
						first = false;
					} else {
						out.write(", ");
					}
					o.accept(new OriginFormattingVisitor(out));
				}
			}
		}
	}

	@Override
	public Void visit(UID uid) throws IOException {
		out.write("symbol");
		writeOrigins(uid);
		return null;
	}

	@Override
	public Void visit(PGoType pGoType) throws IOException {
		out.write("type [");
		out.write(pGoType.toString());
		out.write("]");
		writeOrigins(pGoType);
		return null;
	}

	@Override
	public Void visit(OperatorAccessor operatorAccessor) throws IOException {
		out.write("TLA operator");
		writeOrigins(operatorAccessor);
		return null;
	}

	@Override
	public Void visit(PGoTypeMonomorphicConstraint pGoTypeMonomorphicConstraint) throws IOException {
		out.write("type constraint");
		writeOrigins(pGoTypeMonomorphicConstraint);
		return null;
	}

	@Override
	public Void visit(PGoTypePolymorphicConstraint pGoTypePolymorphicConstraint) throws IOException {
		out.write("polymorphic type constraint");
		writeOrigins(pGoTypePolymorphicConstraint);
		return null;
	}
}
