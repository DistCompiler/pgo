package pgo.formatters;

import java.io.IOException;

import pgo.model.golang.AnonymousFunction;
import pgo.model.golang.Binop;
import pgo.model.golang.Builtins.BuiltinConstant;
import pgo.model.golang.Call;
import pgo.model.golang.ExpressionVisitor;
import pgo.model.golang.GoTo;
import pgo.model.golang.Index;
import pgo.model.golang.IntLiteral;
import pgo.model.golang.Make;
import pgo.model.golang.MapLiteral;
import pgo.model.golang.Selector;
import pgo.model.golang.SliceLiteral;
import pgo.model.golang.SliceOperator;
import pgo.model.golang.StringLiteral;
import pgo.model.golang.StructLiteral;
import pgo.model.golang.TypeAssertion;
import pgo.model.golang.TypeCast;
import pgo.model.golang.Unary;
import pgo.model.golang.VariableName;

public class GoExpressionFormattingVisitor extends ExpressionVisitor<Void, IOException> {

	private IndentingWriter out;

	public GoExpressionFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(VariableName v) throws IOException {
		out.write(v.getName());
		return null;
	}

	@Override
	public Void visit(BuiltinConstant v) throws IOException {
		out.write(v.getValue());
		return null;
	}

	@Override
	public Void visit(IntLiteral intLiteral) throws IOException {
		out.write(Integer.toString(intLiteral.getValue()));
		return null;
	}

	@Override
	public Void visit(MapLiteral mapConstructor) throws IOException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(StringLiteral stringLiteral) throws IOException {
		out.write("\"");
		out.write(stringLiteral.getValue()); // TODO escaping
		out.write("\"");
		return null;
	}

	@Override
	public Void visit(Index index) throws IOException {
		index.getTarget().accept(this);
		out.write("[");
		index.getIndex().accept(this);
		out.write("]");
		return null;
	}

	@Override
	public Void visit(SliceOperator slice) throws IOException {
		slice.getTarget().accept(this);
		out.write("[");
		if (slice.getLow() != null) {
			slice.getLow().accept(this);
		}
		out.write(":");
		if (slice.getHigh() != null) {
			slice.getHigh().accept(this);
		}
		if (slice.getMax() != null) {
			out.write(":");
			slice.getMax().accept(this);
		}
		out.write("]");
		return null;
	}

	@Override
	public Void visit(SliceLiteral sliceConstructor) throws IOException {
		out.write("[]");
		sliceConstructor.getElementType().accept(new GoTypeFormattingVisitor(out));
		out.write("{");
		FormattingTools.writeCommaSeparated(out, sliceConstructor.getInitializers(), expr -> {
			expr.accept(this);
		});
		out.write("}");
		return null;
	}

	@Override
	public Void visit(GoTo goTo) throws IOException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(TypeAssertion typeAssertion) throws IOException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(AnonymousFunction anonymousFunction) throws IOException {
		out.write("func (");
		FormattingTools.writeCommaSeparated(out, anonymousFunction.getArguments(), arg -> {
			arg.accept(new GoNodeFormattingVisitor(out));
		});
		out.write(") ");
		if(!anonymousFunction.getReturnTypes().isEmpty()) {
			out.write("(");
			FormattingTools.writeCommaSeparated(out, anonymousFunction.getReturnTypes(), ret -> {
				if(ret.getName() != null) {
					out.write(ret.getName());
					out.write(" ");
				}
				ret.getType().accept(new GoTypeFormattingVisitor(out));
			});
			out.write(") ");
		}
		
		anonymousFunction.getBody().accept(new GoStatementFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(Call call) throws IOException {
		call.getTarget().accept(this);
		out.write("(");
		FormattingTools.writeCommaSeparated(out, call.getArguments(), arg -> arg.accept(this));
		if (call.hasEllipsis()) {
			out.write("...");
		}
		out.write(")");
		return null;
	}

	@Override
	public Void visit(TypeCast typeCast) throws IOException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(StructLiteral structLiteral) throws IOException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(Binop binop) throws IOException {
		out.write("(");
		binop.getLHS().accept(this);
		out.write(") ");
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
			throw new RuntimeException("unreachable");
		}
		out.write(" (");
		binop.getRHS().accept(this);
		out.write(")");
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
				throw new RuntimeException("unreachable");
		}
		unary.getTarget().accept(this);
		return null;
	}

	@Override
	public Void visit(Selector dot) throws IOException {
		dot.getLHS().accept(this);
		out.write(".");
		out.write(dot.getName());
		return null;
	}

	@Override
	public Void visit(Make make) throws IOException {
		out.write("make(");
		make.getType().accept(new GoTypeFormattingVisitor(out));
		if(make.getSize() != null) {
			out.write(", ");
			make.getSize().accept(this);
		}
		if(make.getCapacity() != null) {
			out.write(", ");
			make.getCapacity().accept(this);
		}
		out.write(")");
		return null;
	}

}
