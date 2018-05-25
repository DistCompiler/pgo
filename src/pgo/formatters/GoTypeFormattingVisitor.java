package pgo.formatters;

import java.io.IOException;

import pgo.model.golang.InterfaceType;
import pgo.model.golang.PtrType;
import pgo.model.golang.SliceType;
import pgo.model.golang.StructType;
import pgo.model.golang.TypeName;
import pgo.model.golang.TypeVisitor;

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
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(PtrType ptrType) throws IOException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(SliceType sliceType) throws IOException {
		out.write("[]");
		sliceType.getElementType().accept(this);
		return null;
	}

	@Override
	public Void visit(InterfaceType interfaceType) throws IOException {
		// TODO: complete this
		out.write("interface{}");
		return null;
	}

}
