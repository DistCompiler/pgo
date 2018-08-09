package pgo.model.golang;

public abstract class GoExpressionVisitor<T, E extends Throwable> {
	public abstract T visit(GoVariableName v) throws E;
	public abstract T visit(GoBuiltins.BuiltinConstant v) throws E;
	public abstract T visit(GoIntLiteral intLiteral) throws E;
	public abstract T visit(GoMapLiteral mapConstructor) throws E;
	public abstract T visit(GoStringLiteral stringLiteral) throws E;
	public abstract T visit(GoIndexExpression index) throws E;
	public abstract T visit(GoSliceOperator slice) throws E;
	public abstract T visit(GoSliceLiteral sliceConstructor) throws E;
	public abstract T visit(GoTypeAssertion typeAssertion) throws E;
	public abstract T visit(GoAnonymousFunction anonymousFunction) throws E;
	public abstract T visit(GoCall call) throws E;
	public abstract T visit(GoTypeCast typeCast) throws E;
	public abstract T visit(GoStructLiteral structLiteral) throws E;
	public abstract T visit(GoBinop binop) throws E;
	public abstract T visit(GoUnary unary) throws E;
	public abstract T visit(GoSelectorExpression dot) throws E;
	public abstract T visit(GoMakeExpression make) throws E;
}
