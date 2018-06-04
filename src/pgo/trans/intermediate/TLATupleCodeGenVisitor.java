package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.List;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.model.golang.*;

public class TLATupleCodeGenVisitor extends TypeVisitor<Expression, RuntimeException> {

	private BlockBuilder builder;
	private List<Expression> elements;

	public TLATupleCodeGenVisitor(BlockBuilder builder, List<Expression> elements) {
		this.builder = builder;
		this.elements = elements;
	}

	@Override
	public Expression visit(TypeName typeName) throws RuntimeException {
		throw new InternalCompilerError();
	}

	@Override
	public Expression visit(StructType structType) throws RuntimeException {
		List<StructLiteralField> fields = new ArrayList<>();
		for(Expression element : elements){
			fields.add(new StructLiteralField(null, element));
		}
		return new StructLiteral(structType, fields);
	}

	@Override
	public Expression visit(PtrType ptrType) throws RuntimeException {
		throw new InternalCompilerError();
	}

	@Override
	public Expression visit(SliceType sliceType) throws RuntimeException {
		return new SliceLiteral(sliceType.getElementType(), elements);
	}

	@Override
	public Expression visit(ChanType chanType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(InterfaceType interfaceType) throws RuntimeException {
		throw new InternalCompilerError();
	}

}
