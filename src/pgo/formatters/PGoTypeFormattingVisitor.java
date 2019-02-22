package pgo.formatters;

import pgo.model.type.*;

import java.io.IOException;

public class PGoTypeFormattingVisitor extends PGoTypeVisitor<Void, IOException> {
	private final IndentingWriter out;

	public PGoTypeFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(PGoTypeAbstractRecord pGoTypeAbstractRecord) throws IOException {
		out.write("AbstractRecord");
		return null;
	}

	@Override
	public Void visit(PGoTypeVariable pGoTypeVariable) throws IOException {
		out.write(pGoTypeVariable.getName());
		return null;
	}

	@Override
	public Void visit(PGoTypeTuple pGoTypeTuple) throws IOException {
		out.write("Tuple[");
		FormattingTools.writeCommaSeparated(out, pGoTypeTuple.getElementTypes(), t -> t.accept(this));
		out.write("]");
		return null;
	}

	@Override
	public Void visit(PGoTypeString pGoTypeString) throws IOException {
		out.write("String");
		return null;
	}

	@Override
	public Void visit(PGoTypeSet pGoTypeSet) throws IOException {
		out.write("Set[");
		pGoTypeSet.getElementType().accept(this);
		out.write("]");
		return null;
	}

	@Override
	public Void visit(PGoTypeNonEnumerableSet pGoTypeNonEnumerableSet) throws IOException {
		out.write("NonEnumerableSet[");
		pGoTypeNonEnumerableSet.getElementType().accept(this);
		out.write("]");
		return null;
	}

	@Override
	public Void visit(PGoTypeBool pGoTypeBool) throws IOException {
		out.write("Bool");
		return null;
	}

	@Override
	public Void visit(PGoTypeReal pGoTypeReal) throws IOException {
		out.write("Real");
		return null;
	}

	@Override
	public Void visit(PGoTypeFunction pGoTypeFunction) throws IOException {
		out.write("Func(");
		FormattingTools.writeCommaSeparated(out, pGoTypeFunction.getParamTypes(), p -> p.accept(this));
		out.write(") ");
		pGoTypeFunction.getReturnType().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTypeChan pGoTypeChan) throws IOException {
		out.write("Chan[");
		pGoTypeChan.getElementType().accept(this);
		out.write("]");
		return null;
	}

	@Override
	public Void visit(PGoTypeInt pGoTypeInt) throws IOException {
		out.write("Int");
		return null;
	}

	@Override
	public Void visit(PGoTypeInterface pGoTypeInterface) throws IOException {
		out.write("Interface{}");
		return null;
	}

	@Override
	public Void visit(PGoTypeMap pGoTypeMap) throws IOException {
		out.write("Map[");
		pGoTypeMap.getKeyType().accept(this);
		out.write("]");
		pGoTypeMap.getValueType().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTypeSlice pGoTypeSlice) throws IOException {
		out.write("Slice[");
		pGoTypeSlice.getElementType().accept(this);
		out.write("]");
		return null;
	}

	@Override
	public Void visit(PGoTypeProcedure pGoTypeProcedure) throws IOException {
		out.write("PlusCalProcedure(");
		FormattingTools.writeCommaSeparated(out, pGoTypeProcedure.getParamTypes(), p -> p.accept(this));
		out.write(")");
		return null;
	}

	@Override
	public Void visit(PGoTypeConcreteRecord pGoTypeConcreteRecord) throws IOException {
		out.write("Record[");
		FormattingTools.writeCommaSeparated(out, pGoTypeConcreteRecord.getFields(), f -> {
			out.write(f.getName());
			out.write(" : ");
			f.getType().accept(this);
		});
		out.write("]");
		return null;
	}
}
