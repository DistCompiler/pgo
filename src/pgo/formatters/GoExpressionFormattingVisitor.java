package pgo.formatters;

import java.io.IOException;

import pgo.TODO;
import pgo.Unreachable;
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
		throw new TODO();
	}

	@Override
	public Void visit(StringLiteral stringLiteral) throws IOException {
		out.write("\"");
		out.write(stringLiteral.getValue().replace("\"", "\\\"")); // TODO escaping
		out.write("\"");
		return null;
	}

	@Override
	public Void visit(Index index) throws IOException {
		index.getTarget().accept(new GoBinopFormattingVisitor(out, 6));
		out.write("[");
		index.getIndex().accept(this);
		out.write("]");
		return null;
	}

	@Override
	public Void visit(SliceOperator slice) throws IOException {
		slice.getTarget().accept(new GoBinopFormattingVisitor(out, 6));
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
	public Void visit(TypeAssertion typeAssertion) throws IOException {
		throw new TODO();
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
		call.getTarget().accept(new GoBinopFormattingVisitor(out, 6));
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
		throw new TODO();
	}

	@Override
	public Void visit(StructLiteral structLiteral) throws IOException {
		structLiteral.getType().accept(new GoTypeFormattingVisitor(out));
		out.write("{");
		FormattingTools.writeCommaSeparated(out, structLiteral.getFields(), field -> {
			if(field.getName() != null){
				out.write(field.getName());
				out.write(": ");
			}
			field.getValue().accept(this);
		});
		out.write("}");
		return null;
	}

	@Override
	public Void visit(Binop binop) throws IOException {
		binop.accept(new GoBinopFormattingVisitor(out, 0));
		return null;
	}

	@Override
	public Void visit(Unary unary) throws IOException {
		unary.accept(new GoBinopFormattingVisitor(out, 0));
		return null;
	}

	@Override
	public Void visit(Selector dot) throws IOException {
		dot.getLHS().accept(new GoBinopFormattingVisitor(out, 6));
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
