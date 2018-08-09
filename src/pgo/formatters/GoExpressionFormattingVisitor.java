package pgo.formatters;

import java.io.IOException;
import java.util.Map;

import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.golang.GoBuiltins.BuiltinConstant;
import pgo.model.golang.type.GoMapType;

public class GoExpressionFormattingVisitor extends GoExpressionVisitor<Void, IOException> {

	private IndentingWriter out;

	public GoExpressionFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(GoVariableName v) throws IOException {
		out.write(v.getName());
		return null;
	}

	@Override
	public Void visit(BuiltinConstant v) throws IOException {
		out.write(v.getValue());
		return null;
	}

	@Override
	public Void visit(GoIntLiteral intLiteral) throws IOException {
		out.write(Integer.toString(intLiteral.getValue()));
		return null;
	}

	@Override
	public Void visit(GoMapLiteral mapConstructor) throws IOException {
		(new GoMapType(mapConstructor.getKeyType(), mapConstructor.getValueType()))
				.accept(new GoTypeFormattingVisitor(out));
		out.write("{");
		out.newLine();
		for (Map.Entry<GoExpression, GoExpression> entry : mapConstructor.getPairs().entrySet()) {
			entry.getKey().accept(this);
			out.write(": ");
			entry.getValue().accept(this);
			out.write(",");
			out.newLine();
		}
		out.write("}");
		return null;
	}

	@Override
	public Void visit(GoStringLiteral stringLiteral) throws IOException {
		out.write("\"");
		out.write(stringLiteral.getValue().replace("\"", "\\\"")); // TODO escaping
		out.write("\"");
		return null;
	}

	@Override
	public Void visit(GoIndexExpression index) throws IOException {
		index.getTarget().accept(new GoBinopFormattingVisitor(out, 6));
		out.write("[");
		index.getIndex().accept(this);
		out.write("]");
		return null;
	}

	@Override
	public Void visit(GoSliceOperator slice) throws IOException {
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
	public Void visit(GoSliceLiteral sliceConstructor) throws IOException {
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
	public Void visit(GoTypeAssertion typeAssertion) throws IOException {
		typeAssertion.getTarget().accept(this);
		out.write(".(");
		typeAssertion.getType().accept(new GoTypeFormattingVisitor(out));
		out.write(")");
		return null;
	}

	@Override
	public Void visit(GoAnonymousFunction anonymousFunction) throws IOException {
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
	public Void visit(GoCall call) throws IOException {
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
	public Void visit(GoTypeCast typeCast) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(GoStructLiteral structLiteral) throws IOException {
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
	public Void visit(GoBinop binop) throws IOException {
		binop.accept(new GoBinopFormattingVisitor(out, 0));
		return null;
	}

	@Override
	public Void visit(GoUnary unary) throws IOException {
		unary.accept(new GoBinopFormattingVisitor(out, 0));
		return null;
	}

	@Override
	public Void visit(GoSelectorExpression dot) throws IOException {
		dot.getLHS().accept(new GoBinopFormattingVisitor(out, 6));
		out.write(".");
		out.write(dot.getName());
		return null;
	}

	@Override
	public Void visit(GoMakeExpression make) throws IOException {
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
