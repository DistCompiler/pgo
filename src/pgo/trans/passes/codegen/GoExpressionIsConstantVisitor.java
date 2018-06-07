package pgo.trans.passes.codegen;

import pgo.TODO;
import pgo.model.golang.*;

import java.util.function.Function;
import java.util.function.ToDoubleBiFunction;

public class GoExpressionIsConstantVisitor extends ExpressionVisitor<Boolean, RuntimeException> {
	@Override
	public Boolean visit(VariableName v) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(Builtins.BuiltinConstant v) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(IntLiteral intLiteral) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(MapLiteral mapConstructor) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Boolean visit(StringLiteral stringLiteral) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(Index index) throws RuntimeException {
		return index.getTarget().accept(this) && index.getIndex().accept(this);
	}

	@Override
	public Boolean visit(SliceOperator slice) throws RuntimeException {
		Function<Expression, Boolean> nullOrConst = exp -> exp != null ? exp.accept(this) : true;
		return slice.getTarget().accept(this) && nullOrConst.apply(slice.getLow())
				&& nullOrConst.apply(slice.getHigh()) && nullOrConst.apply(slice.getMax());
	}

	@Override
	public Boolean visit(SliceLiteral sliceConstructor) throws RuntimeException {
		return sliceConstructor.getInitializers().stream().allMatch(exp -> exp.accept(this));
	}

	@Override
	public Boolean visit(TypeAssertion typeAssertion) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(AnonymousFunction anonymousFunction) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(Call call) throws RuntimeException {
		return call.getTarget().accept(this) && call.getArguments().stream().allMatch(exp -> exp.accept(this));
	}

	@Override
	public Boolean visit(TypeCast typeCast) throws RuntimeException {
		return typeCast.getTarget().accept(this);
	}

	@Override
	public Boolean visit(StructLiteral structLiteral) throws RuntimeException {
		return structLiteral.getFields().stream().allMatch(field -> field.getValue().accept(this));
	}

	@Override
	public Boolean visit(Binop binop) throws RuntimeException {
		return binop.getLHS().accept(this) && binop.getRHS().accept(this);
	}

	@Override
	public Boolean visit(Unary unary) throws RuntimeException {
		return unary.getTarget().accept(this);
	}

	@Override
	public Boolean visit(Selector dot) throws RuntimeException {
		return dot.getLHS().accept(this);
	}

	@Override
	public Boolean visit(Make make) throws RuntimeException {
		return (make.getCapacity() != null ? make.getCapacity().accept(this) : true)
				&& (make.getSize() != null ? make.getSize().accept(this) : true);
	}
}
