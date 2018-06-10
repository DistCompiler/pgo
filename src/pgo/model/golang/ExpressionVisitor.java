package pgo.model.golang;

public abstract class ExpressionVisitor<T, E extends Throwable> {
	public abstract T visit(VariableName v) throws E;
	public abstract T visit(Builtins.BuiltinConstant v) throws E;
	public abstract T visit(IntLiteral intLiteral) throws E;
	public abstract T visit(MapLiteral mapConstructor) throws E;
	public abstract T visit(StringLiteral stringLiteral) throws E;
	public abstract T visit(Index index) throws E;
	public abstract T visit(SliceOperator slice) throws E;
	public abstract T visit(SliceLiteral sliceConstructor) throws E;
	public abstract T visit(TypeAssertion typeAssertion) throws E;
	public abstract T visit(AnonymousFunction anonymousFunction) throws E;
	public abstract T visit(Call call) throws E;
	public abstract T visit(TypeCast typeCast) throws E;
	public abstract T visit(StructLiteral structLiteral) throws E;
	public abstract T visit(Binop binop) throws E;
	public abstract T visit(Unary unary) throws E;
	public abstract T visit(Selector dot) throws E;
	public abstract T visit(Make make) throws E;
}
