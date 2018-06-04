package pgo.formatters;

import pgo.Unreachable;
import pgo.model.golang.*;

import java.io.IOException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

public class GoBinopFormattingVisitor extends ExpressionVisitor<Void, IOException> {

	private final IndentingWriter out;
	private final int precedence;

	private static Map<Binop.Operation, Integer> operatorPrecedence = new HashMap<>();
	static{
		// *  /  %  <<  >>  &  &^
		for(Binop.Operation op : Arrays.asList(
				Binop.Operation.TIMES, Binop.Operation.DIVIDE,
				Binop.Operation.MOD, Binop.Operation.LSHIFT,
				Binop.Operation.RSHIFT, Binop.Operation.BAND,
				Binop.Operation.BCLEAR)){
			operatorPrecedence.put(op, 5);
		}
		// +  -  |  ^
		for(Binop.Operation op : Arrays.asList(Binop.Operation.PLUS, Binop.Operation.MINUS,
				Binop.Operation.BOR, Binop.Operation.BXOR)){
			operatorPrecedence.put(op, 4);
		}
		// ==  !=  <  <=  >  >=
		for(Binop.Operation op : Arrays.asList(Binop.Operation.EQ, Binop.Operation.NEQ,
				Binop.Operation.LT, Binop.Operation.LEQ,
				Binop.Operation.GT, Binop.Operation.GEQ)){
			operatorPrecedence.put(op, 3);
		}
		// &&
		operatorPrecedence.put(Binop.Operation.AND, 2);
		// ||
		operatorPrecedence.put(Binop.Operation.OR, 1);
	}

	public GoBinopFormattingVisitor(IndentingWriter out, int precedence){
		this.out = out;
		this.precedence = precedence;
	}

	@Override
	public Void visit(VariableName v) throws IOException {
		v.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(Builtins.BuiltinConstant v) throws IOException {
		v.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(IntLiteral intLiteral) throws IOException {
		intLiteral.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(MapLiteral mapConstructor) throws IOException {
		mapConstructor.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(StringLiteral stringLiteral) throws IOException {
		stringLiteral.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(Index index) throws IOException {
		index.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(SliceOperator slice) throws IOException {
		slice.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(SliceLiteral sliceConstructor) throws IOException {
		sliceConstructor.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TypeAssertion typeAssertion) throws IOException {
		typeAssertion.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(AnonymousFunction anonymousFunction) throws IOException {
		anonymousFunction.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(Call call) throws IOException {
		call.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TypeCast typeCast) throws IOException {
		typeCast.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(StructLiteral structLiteral) throws IOException {
		structLiteral.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(Binop binop) throws IOException {
		int newPrecedence = operatorPrecedence.get(binop.getOperation());
		if(newPrecedence <= precedence){
			out.write("(");
		}
		binop.getLHS().accept(new GoBinopFormattingVisitor(out, newPrecedence));
		out.write(" ");
		switch(binop.getOperation()) {
			case AND:
				out.write("&&");
				break;
			case BAND:
				out.write("&");
				break;
			case BCLEAR:
				out.write("&^");
				break;
			case BOR:
				out.write("|");
				break;
			case BXOR:
				out.write("^");
				break;
			case DIVIDE:
				out.write("/");
				break;
			case EQ:
				out.write("==");
				break;
			case GEQ:
				out.write(">=");
				break;
			case GT:
				out.write(">");
				break;
			case LEQ:
				out.write("<=");
				break;
			case LSHIFT:
				out.write("<<");
				break;
			case LT:
				out.write("<");
				break;
			case MINUS:
				out.write("-");
				break;
			case MOD:
				out.write("%");
				break;
			case NEQ:
				out.write("!=");
				break;
			case OR:
				out.write("||");
				break;
			case PLUS:
				out.write("+");
				break;
			case RSHIFT:
				out.write(">>");
				break;
			case TIMES:
				out.write("*");
				break;
			default:
				throw new Unreachable();
		}
		out.write(" ");
		binop.getRHS().accept(new GoBinopFormattingVisitor(out, newPrecedence));
		if(newPrecedence <= precedence){
			out.write(")");
		}
		return null;
	}

	@Override
	public Void visit(Unary unary) throws IOException {
		switch (unary.getOperation()) {
			case POS:
				out.write("+");
				break;
			case NEG:
				out.write("-");
				break;
			case NOT:
				out.write("!");
				break;
			case COMPLEMENT:
				out.write("^");
				break;
			case DEREF:
				out.write("*");
				break;
			case ADDR:
				out.write("&");
				break;
			case RECV:
				out.write("<-");
				break;
			default:
				throw new Unreachable();
		}
		unary.getTarget().accept(new GoBinopFormattingVisitor(out, 6)); // max precedence + 1
		return null;
	}

	@Override
	public Void visit(Selector dot) throws IOException {
		dot.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(Make make) throws IOException {
		make.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}
}
