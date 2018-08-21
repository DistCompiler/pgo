package pgo.trans.passes.codegen;

import pgo.TODO;
import pgo.model.golang.*;

import java.util.function.Function;

public class GoExpressionIsConstantVisitor extends GoExpressionVisitor<Boolean, RuntimeException> {
	@Override
	public Boolean visit(GoVariableName v) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(GoBuiltins.BuiltinConstant v) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(GoIntLiteral intLiteral) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(GoMapLiteral mapConstructor) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Boolean visit(GoStringLiteral stringLiteral) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(GoIndexExpression index) throws RuntimeException {
		return index.getTarget().accept(this) && index.getIndex().accept(this);
	}

	@Override
	public Boolean visit(GoSliceOperator slice) throws RuntimeException {
		Function<GoExpression, Boolean> nullOrConst = exp -> exp != null ? exp.accept(this) : true;
		return slice.getTarget().accept(this) && nullOrConst.apply(slice.getLow())
				&& nullOrConst.apply(slice.getHigh()) && nullOrConst.apply(slice.getMax());
	}

	@Override
	public Boolean visit(GoSliceLiteral sliceConstructor) throws RuntimeException {
		return sliceConstructor.getInitializers().stream().allMatch(exp -> exp.accept(this));
	}

	@Override
	public Boolean visit(GoTypeAssertion typeAssertion) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(GoAnonymousFunction anonymousFunction) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(GoCall call) throws RuntimeException {
		return call.getTarget().accept(this) && call.getArguments().stream().allMatch(exp -> exp.accept(this));
	}

	@Override
	public Boolean visit(GoTypeCast typeCast) throws RuntimeException {
		return typeCast.getTarget().accept(this);
	}

	@Override
	public Boolean visit(GoStructLiteral structLiteral) throws RuntimeException {
		return structLiteral.getFields().stream().allMatch(field -> field.getValue().accept(this));
	}

	@Override
	public Boolean visit(GoBinop binop) throws RuntimeException {
		return binop.getLHS().accept(this) && binop.getRHS().accept(this);
	}

	@Override
	public Boolean visit(GoUnary unary) throws RuntimeException {
		return unary.getTarget().accept(this);
	}

	@Override
	public Boolean visit(GoSelectorExpression dot) throws RuntimeException {
		return dot.getLHS().accept(this);
	}

	@Override
	public Boolean visit(GoMakeExpression make) throws RuntimeException {
		return (make.getCapacity() != null ? make.getCapacity().accept(this) : true)
				&& (make.getSize() != null ? make.getSize().accept(this) : true);
	}
}
