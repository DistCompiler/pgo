package pgo.formatters;

import pgo.model.type.*;

import java.io.IOException;

public class TypeFormattingVisitor extends TypeVisitor<Void, IOException> {
	private final IndentingWriter out;

	public TypeFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(AbstractRecordType abstractRecordType) throws IOException {
		out.write("AbstractRecord");
		return null;
	}

	@Override
	public Void visit(ArchetypeResourceType archetypeResourceType) throws IOException {
		out.write("ArchetypeResource read (");
		archetypeResourceType.getReadType().accept(this);
		out.write(") write (");
		archetypeResourceType.getWriteType().accept(this);
		out.write(")");
		return null;
	}

	@Override
	public Void visit(ArchetypeResourceCollectionType archetypeResourceCollectionType) throws IOException {
		out.write("ArchetypeResourceCollection[");
		archetypeResourceCollectionType.getKeyType().accept(this);
		out.write("]read (");
		archetypeResourceCollectionType.getReadType().accept(this);
		out.write(") write (");
		archetypeResourceCollectionType.getWriteType().accept(this);
		out.write(")");
		return null;
	}

	@Override
	public Void visit(TypeVariable typeVariable) throws IOException {
		out.write(typeVariable.getName());
		return null;
	}

	@Override
	public Void visit(TupleType tupleType) throws IOException {
		out.write("Tuple[");
		FormattingTools.writeCommaSeparated(out, tupleType.getElementTypes(), t -> t.accept(this));
		out.write("]");
		return null;
	}

	@Override
	public Void visit(StringType stringType) throws IOException {
		out.write("String");
		return null;
	}

	@Override
	public Void visit(SetType setType) throws IOException {
		out.write("Set[");
		setType.getElementType().accept(this);
		out.write("]");
		return null;
	}

	@Override
	public Void visit(NonEnumerableSetType nonEnumerableSetType) throws IOException {
		out.write("NonEnumerableSet[");
		nonEnumerableSetType.getElementType().accept(this);
		out.write("]");
		return null;
	}

	@Override
	public Void visit(BoolType boolType) throws IOException {
		out.write("Bool");
		return null;
	}

	@Override
	public Void visit(RealType realType) throws IOException {
		out.write("Real");
		return null;
	}

	@Override
	public Void visit(FunctionType functionType) throws IOException {
		out.write("Func(");
		FormattingTools.writeCommaSeparated(out, functionType.getParamTypes(), p -> p.accept(this));
		out.write(") ");
		functionType.getReturnType().accept(this);
		return null;
	}

	@Override
	public Void visit(ChanType chanType) throws IOException {
		out.write("Chan[");
		chanType.getElementType().accept(this);
		out.write("]");
		return null;
	}

	@Override
	public Void visit(IntType intType) throws IOException {
		out.write("Int");
		return null;
	}

	@Override
	public Void visit(InterfaceType interfaceType) throws IOException {
		out.write("Interface{}");
		return null;
	}

	@Override
	public Void visit(MapType mapType) throws IOException {
		out.write("Map[");
		mapType.getKeyType().accept(this);
		out.write("]");
		mapType.getValueType().accept(this);
		return null;
	}

	@Override
	public Void visit(SliceType sliceType) throws IOException {
		out.write("Slice[");
		sliceType.getElementType().accept(this);
		out.write("]");
		return null;
	}

	@Override
	public Void visit(ProcedureType procedureType) throws IOException {
		out.write("PlusCalProcedure(");
		FormattingTools.writeCommaSeparated(out, procedureType.getParamTypes(), p -> p.accept(this));
		out.write(")");
		return null;
	}

	@Override
	public Void visit(RecordType recordType) throws IOException {
		out.write("Record[");
		FormattingTools.writeCommaSeparated(out, recordType.getFields(), f -> {
			out.write(f.getName());
			out.write(" : ");
			f.getType().accept(this);
		});
		out.write("]");
		return null;
	}
}
