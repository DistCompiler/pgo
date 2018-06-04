package pgo.formatters;

import java.io.IOException;

import pgo.TODO;
import pgo.model.golang.*;

public class GoTypeFormattingVisitor extends TypeVisitor<Void, IOException> {

	private IndentingWriter out;

	public GoTypeFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(TypeName typeName) throws IOException {
		out.write(typeName.getName());
		return null;
	}

	@Override
	public Void visit(StructType structType) throws IOException {
		out.write("struct{");
		for(StructTypeField field : structType.getFields()){
			out.write(field.getName());
			out.write(" ");
			field.getType().accept(this);
			out.write("; ");
		}
		out.write("}");
		return null;
	}

	@Override
	public Void visit(PtrType ptrType) throws IOException {
		out.write("*");
		ptrType.getPointee().accept(this);
		return null;
	}

	@Override
	public Void visit(SliceType sliceType) throws IOException {
		out.write("[]");
		sliceType.getElementType().accept(this);
		return null;
	}

	@Override
	public Void visit(ChanType chanType) throws IOException {
		out.write("chan ");
		chanType.getElementType().accept(this);
		return null;
	}

	@Override
	public Void visit(InterfaceType interfaceType) throws IOException {
		// TODO: complete this
		out.write("interface{}");
		return null;
	}

}
