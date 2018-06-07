package pgo.trans.passes.codegen;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.model.golang.*;

import java.util.List;

public class GoExpressionStaticComparisonVisitor extends ExpressionVisitor<Integer, RuntimeException> {

	private final Expression rhs;

	public GoExpressionStaticComparisonVisitor(Expression rhs) {
		this.rhs = rhs;
	}

	@Override
	public Integer visit(VariableName v) throws RuntimeException {
		throw new InternalCompilerError();
	}

	private <T> T getRhs(Expression lhs){
		if(lhs.getClass().isInstance(rhs)){
			return (T)rhs;
		}
		throw new InternalCompilerError();
	}

	@Override
	public Integer visit(Builtins.BuiltinConstant v) throws RuntimeException {
		Builtins.BuiltinConstant rhs = getRhs(v);
		if(v.getValue().equals(rhs.getValue())) return 0;
		if(rhs.getValue().equals("true")) return -1;
		if(rhs.getValue().equals("false")) return 1;
		throw new InternalCompilerError();
	}

	@Override
	public Integer visit(IntLiteral intLiteral) throws RuntimeException {
		IntLiteral rhs = getRhs(intLiteral);
		return intLiteral.getValue() - rhs.getValue();
	}

	@Override
	public Integer visit(MapLiteral mapConstructor) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(StringLiteral stringLiteral) throws RuntimeException {
		StringLiteral rhs = getRhs(stringLiteral);
		return stringLiteral.getValue().compareTo(rhs.getValue());
	}

	@Override
	public Integer visit(Index index) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(SliceOperator slice) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(SliceLiteral sliceConstructor) throws RuntimeException {
		SliceLiteral rhs = getRhs(sliceConstructor);
		List<Expression> lhsInitializers = sliceConstructor.getInitializers();
		List<Expression> rhsInitializers = rhs.getInitializers();
		int sizeDiff = lhsInitializers.size() - rhsInitializers.size();
		if(sizeDiff == 0){
			for(int i = 0; i < lhsInitializers.size(); ++i){
				int elementDiff = lhsInitializers.get(i).accept(
						new GoExpressionStaticComparisonVisitor(rhsInitializers.get(i)));
				if(elementDiff != 0){
					return elementDiff;
				}
			}
			return 0;
		}else{
			return sizeDiff;
		}
	}

	@Override
	public Integer visit(TypeAssertion typeAssertion) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(AnonymousFunction anonymousFunction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(Call call) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(TypeCast typeCast) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(StructLiteral structLiteral) throws RuntimeException {
		StructLiteral rhs = getRhs(structLiteral);
		// TODO: this only works is all fields are specified
		List<StructLiteralField> lhsFields = structLiteral.getFields();
		List<StructLiteralField> rhsFields = rhs.getFields();
		if(lhsFields.size() != rhsFields.size()){
			throw new InternalCompilerError();
		}
		for(int i = 0; i < lhsFields.size(); ++i){
			int elementDiff = lhsFields.get(i).getValue().accept(
					new GoExpressionStaticComparisonVisitor(rhsFields.get(i).getValue()));
			if(elementDiff != 0){
				return elementDiff;
			}
		}
		return 0;
	}

	@Override
	public Integer visit(Binop binop) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(Unary unary) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(Selector dot) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(Make make) throws RuntimeException {
		throw new TODO();
	}
}
