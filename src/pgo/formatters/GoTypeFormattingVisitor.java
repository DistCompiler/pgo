package pgo.formatters;

import pgo.TODO;
import pgo.model.golang.GoPtrType;
import pgo.model.golang.type.*;

import java.io.IOException;

public class GoTypeFormattingVisitor extends GoTypeVisitor<Void, IOException> {

	private IndentingWriter out;

	public GoTypeFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(GoTypeName typeName) throws IOException {
		out.write(typeName.getName());
		return null;
	}

	@Override
	public Void visit(GoArchetypeResourceType archetypeResourceType) throws IOException {
		out.write("ArchetypeResource[read: ");
		archetypeResourceType.getReadType().accept(this);
		out.write(", write: ");
		archetypeResourceType.getWriteType().accept(this);
		out.write("]");

		return null;
	}

	@Override
	public Void visit(GoArchetypeResourceCollectionType archetypeResourceCollectionType) throws IOException {
		out.write("ArchetypeResourceCollection[key: ");
		archetypeResourceCollectionType.getKeyType().accept(this);
		out.write(", read: ");
		archetypeResourceCollectionType.getReadType().accept(this);
		out.write(", write: ");
		archetypeResourceCollectionType.getWriteType().accept(this);
		out.write("]");

		return null;
	}

	@Override
	public Void visit(GoStructType structType) throws IOException {
		out.write("struct{");
		for(GoStructTypeField field : structType.getFields()){
			out.write(field.getName());
			out.write(" ");
			field.getType().accept(this);
			out.write("; ");
		}
		out.write("}");
		return null;
	}

	@Override
	public Void visit(GoPtrType ptrType) throws IOException {
		out.write("*");
		ptrType.getPointee().accept(this);
		return null;
	}

	@Override
	public Void visit(GoSliceType sliceType) throws IOException {
		out.write("[]");
		sliceType.getElementType().accept(this);
		return null;
	}

	@Override
	public Void visit(GoChanType chanType) throws IOException {
		out.write("chan ");
		chanType.getElementType().accept(this);
		return null;
	}

	@Override
	public Void visit(GoMapType mapType) throws IOException {
		out.write("map[");
		mapType.getKeyType().accept(this);
		out.write("]");
		mapType.getValueType().accept(this);
		return null;
	}

	@Override
	public Void visit(GoInterfaceType interfaceType) throws IOException {
		// TODO: complete this
		out.write("interface{}");
		return null;
	}

}
