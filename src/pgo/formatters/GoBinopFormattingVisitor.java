package pgo.formatters;

import pgo.Unreachable;
import pgo.model.golang.*;

import java.io.IOException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

public class GoBinopFormattingVisitor extends GoExpressionVisitor<Void, IOException> {

	private final IndentingWriter out;
	private final int precedence;

	private static Map<GoBinop.Operation, Integer> operatorPrecedence = new HashMap<>();
	static{
		// *  /  %  <<  >>  &  &^
		for(GoBinop.Operation op : Arrays.asList(
				GoBinop.Operation.TIMES, GoBinop.Operation.DIVIDE,
				GoBinop.Operation.MOD, GoBinop.Operation.LSHIFT,
				GoBinop.Operation.RSHIFT, GoBinop.Operation.BAND,
				GoBinop.Operation.BCLEAR)){
			operatorPrecedence.put(op, 5);
		}
		// +  -  |  ^
		for(GoBinop.Operation op : Arrays.asList(GoBinop.Operation.PLUS, GoBinop.Operation.MINUS,
				GoBinop.Operation.BOR, GoBinop.Operation.BXOR)){
			operatorPrecedence.put(op, 4);
		}
		// ==  !=  <  <=  >  >=
		for(GoBinop.Operation op : Arrays.asList(GoBinop.Operation.EQ, GoBinop.Operation.NEQ,
				GoBinop.Operation.LT, GoBinop.Operation.LEQ,
				GoBinop.Operation.GT, GoBinop.Operation.GEQ)){
			operatorPrecedence.put(op, 3);
		}
		// &&
		operatorPrecedence.put(GoBinop.Operation.AND, 2);
		// ||
		operatorPrecedence.put(GoBinop.Operation.OR, 1);
	}

	public GoBinopFormattingVisitor(IndentingWriter out, int precedence){
		this.out = out;
		this.precedence = precedence;
	}

	@Override
	public Void visit(GoVariableName v) throws IOException {
		v.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoBuiltins.BuiltinConstant v) throws IOException {
		v.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoIntLiteral intLiteral) throws IOException {
		intLiteral.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoMapLiteral mapConstructor) throws IOException {
		mapConstructor.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoStringLiteral stringLiteral) throws IOException {
		stringLiteral.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoIndexExpression index) throws IOException {
		index.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoSliceOperator slice) throws IOException {
		slice.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoSliceLiteral sliceConstructor) throws IOException {
		sliceConstructor.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoTypeAssertion typeAssertion) throws IOException {
		typeAssertion.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoAnonymousFunction anonymousFunction) throws IOException {
		anonymousFunction.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoCall call) throws IOException {
		call.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoTypeCast typeCast) throws IOException {
		typeCast.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoStructLiteral structLiteral) throws IOException {
		structLiteral.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoBinop binop) throws IOException {
		int newPrecedence = operatorPrecedence.get(binop.getOperation());
		int nextPrecedence = newPrecedence;
		if(newPrecedence < precedence){
			nextPrecedence = 0;
			out.write("(");
		}
		binop.getLHS().accept(new GoBinopFormattingVisitor(out, nextPrecedence));
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
		binop.getRHS().accept(new GoBinopFormattingVisitor(out, nextPrecedence));
		if(newPrecedence < precedence){
			out.write(")");
		}
		return null;
	}

	@Override
	public Void visit(GoUnary unary) throws IOException {
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
	public Void visit(GoSelectorExpression dot) throws IOException {
		dot.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoMakeExpression make) throws IOException {
		make.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}
}
