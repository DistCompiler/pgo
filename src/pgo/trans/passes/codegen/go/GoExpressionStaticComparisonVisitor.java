package pgo.trans.passes.codegen.go;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.model.golang.*;

import java.util.List;

public class GoExpressionStaticComparisonVisitor extends GoExpressionVisitor<Integer, RuntimeException> {

	private final GoExpression rhs;

	public GoExpressionStaticComparisonVisitor(GoExpression rhs) {
		this.rhs = rhs;
	}

	@Override
	public Integer visit(GoVariableName v) throws RuntimeException {
		throw new InternalCompilerError();
	}

	private <T> T getRhs(GoExpression lhs){
		if(lhs.getClass().isInstance(rhs)){
			return (T)rhs;
		}
		throw new InternalCompilerError();
	}

	@Override
	public Integer visit(GoBuiltins.BuiltinConstant v) throws RuntimeException {
		GoBuiltins.BuiltinConstant rhs = getRhs(v);
		if(v.getValue().equals(rhs.getValue())) return 0;
		if(rhs.getValue().equals("true")) return -1;
		if(rhs.getValue().equals("false")) return 1;
		throw new InternalCompilerError();
	}

	@Override
	public Integer visit(GoIntLiteral intLiteral) throws RuntimeException {
		GoIntLiteral rhs = getRhs(intLiteral);
		return intLiteral.getValue() - rhs.getValue();
	}

	@Override
	public Integer visit(GoMapLiteral mapConstructor) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(GoStringLiteral stringLiteral) throws RuntimeException {
		GoStringLiteral rhs = getRhs(stringLiteral);
		return stringLiteral.getValue().compareTo(rhs.getValue());
	}

	@Override
	public Integer visit(GoIndexExpression index) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(GoSliceOperator slice) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(GoSliceLiteral sliceConstructor) throws RuntimeException {
		GoSliceLiteral rhs = getRhs(sliceConstructor);
		List<GoExpression> lhsInitializers = sliceConstructor.getInitializers();
		List<GoExpression> rhsInitializers = rhs.getInitializers();
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
	public Integer visit(GoTypeAssertion typeAssertion) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(GoAnonymousFunction anonymousFunction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(GoCall call) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(GoTypeCast typeCast) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(GoStructLiteral structLiteral) throws RuntimeException {
		GoStructLiteral rhs = getRhs(structLiteral);
		// TODO: this only works is all fields are specified
		List<GoStructLiteralField> lhsFields = structLiteral.getFields();
		List<GoStructLiteralField> rhsFields = rhs.getFields();
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
	public Integer visit(GoBinop binop) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(GoUnary unary) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(GoSelectorExpression dot) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Integer visit(GoMakeExpression make) throws RuntimeException {
		throw new TODO();
	}
}
