package pgo.trans.passes.codegen.go;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.type.*;

import java.util.ArrayList;
import java.util.List;

public class TLATupleCodeGenVisitor extends GoTypeVisitor<GoExpression, RuntimeException> {
	private final List<GoExpression> elements;

	public TLATupleCodeGenVisitor(List<GoExpression> elements) {
		this.elements = elements;
	}

	@Override
	public GoExpression visit(GoTypeName typeName) throws RuntimeException {
		throw new InternalCompilerError();
	}

	@Override
	public GoExpression visit(GoStructType structType) throws RuntimeException {
		List<GoStructLiteralField> fields = new ArrayList<>();
		for(GoExpression element : elements){
			fields.add(new GoStructLiteralField(null, element));
		}
		return new GoStructLiteral(structType, fields);
	}

	@Override
	public GoExpression visit(GoPtrType ptrType) throws RuntimeException {
		throw new InternalCompilerError();
	}

	@Override
	public GoExpression visit(GoSliceType sliceType) throws RuntimeException {
		return new GoSliceLiteral(sliceType.getElementType(), elements);
	}

	@Override
	public GoExpression visit(GoChanType chanType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(GoMapType mapType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(GoInterfaceType interfaceType) throws RuntimeException {
		throw new InternalCompilerError();
	}
}
