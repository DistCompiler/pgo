package pgo.model.golang;

/**
 * A Go code expression base class
 * 
 */
public abstract class Expression {
	
	public abstract class Visitor<T> {
		public abstract T visit(VariableName v);
		public abstract T visit(Builtins.BuiltinConstant v);
		public abstract T visit(IntLiteral intLiteral);
		public abstract T visit(MapLiteral mapConstructor);
		public abstract T visit(StringLiteral stringLiteral);
		public abstract T visit(Index index);
		public abstract T visit(SliceOperator slice);
		public abstract T visit(SliceConstructor sliceConstructor);
		public abstract T visit(GoTo goTo);
		public abstract T visit(TypeAssertion typeAssertion);
		public abstract T visit(AnonymousFunction anonymousFunction);
		public abstract T visit(Call call);
		public abstract T visit(TypeCast typeCast);
		public abstract T visit(StructLiteral structLiteral);
		public abstract T visit(Binop binop);
		public abstract T visit(Unary unary);
		public abstract T visit(Dot dot);
	}

	public abstract <T> T accept(Visitor<T> visitor);

}