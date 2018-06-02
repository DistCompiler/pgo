package pgo.formatters;

import java.io.IOException;
import java.util.List;

import pgo.model.golang.*;

public class GoStatementFormattingVisitor extends StatementVisitor<Void, IOException> {

	private IndentingWriter out;

	public GoStatementFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(Comment comment) throws IOException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(Assignment assignment) throws IOException {
		FormattingTools.writeCommaSeparated(out, assignment.getNames(), name -> {
			name.accept(new GoExpressionFormattingVisitor(out));
		});
		if (assignment.isDefinition()) {
			out.write(" := ");
		} else {
			out.write(" = ");
		}
		FormattingTools.writeCommaSeparated(out, assignment.getValues(), val -> {
			val.accept(new GoExpressionFormattingVisitor(out));
		});
		return null;
	}

	@Override
	public Void visit(Return return1) throws IOException {
		out.write("return");
		List<Expression> expressions = return1.getValues();
		if (expressions.size() == 0) {
			return null;
		}
		out.write(" ");
		FormattingTools.writeCommaSeparated(out, expressions, e -> e.accept(new GoExpressionFormattingVisitor(out)));
		return null;
	}

	@Override
	public Void visit(Block block) throws IOException {
		out.write("{");
		out.newLine();
		try (IndentingWriter.Indent ignored = out.indent()) {
			for (Statement stmt : block.getStatements()) {
				stmt.accept(this);
				out.newLine();
			}
		}
		out.write("}");
		return null;
	}

	@Override
	public Void visit(For for1) throws IOException {
		out.write("for ");
		if (for1.getInit() != null) {
			for1.getInit().accept(this);
			out.write("; ");
		}
		if (for1.getCondition() != null) {
			for1.getCondition().accept(new GoExpressionFormattingVisitor(out));
		}
		if (for1.getIncrement() != null) {
			out.write("; ");
			for1.getIncrement().accept(this);
		}
		if (for1.getCondition() != null) {
			out.write(" ");
		}
		for1.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(ForRange forRange) throws IOException {
		out.write("for ");
		FormattingTools.writeCommaSeparated(
				out,
				forRange.getLhs(),
				e -> e.accept(new GoExpressionFormattingVisitor(out)));
		if (forRange.isDefinition()) {
			out.write(" := range ");
		} else {
			out.write(" = range ");
		}
		forRange.getRangeExpr().accept(new GoExpressionFormattingVisitor(out));
		forRange.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(If if1) throws IOException {
		out.write("if ");
		if1.getCond().accept(new GoExpressionFormattingVisitor(out));
		out.write(" ");
		if1.getThen().accept(this);
		if (if1.getElse() != null && !if1.getElse().getStatements().isEmpty()) {
			out.write(" else ");
			if1.getElse().accept(this);
		}
		return null;
	}

	@Override
	public Void visit(Switch switch1) throws IOException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(Label label) throws IOException {
		out.write(label.getName());
		out.write(":");
		return null;
	}

	@Override
	public Void visit(GoCall goCall) throws IOException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(Select select) throws IOException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(GoTo goTo) throws IOException {
		out.write("goto ");
		out.write(goTo.getTo().getName());
		return null;
	}

	@Override
	public Void visit(IncDec incDec) throws IOException {
		incDec.getExpression().accept(new GoExpressionFormattingVisitor(out));
		if (incDec.isInc()) {
			out.write("++");
		} else {
			out.write("--");
		}
		return null;
	}

	@Override
	public Void visit(ExpressionStatement expressionStatement) throws IOException {
		expressionStatement.getExpression().accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(Break break1) throws IOException {
		out.write("break");
		return null;
	}

	@Override
	public Void visit(Continue continue1) throws IOException {
		out.write("continue");
		return null;
	}

	@Override
	public Void visit(Defer defer) throws IOException {
		out.write("defer ");
		defer.getExpression().accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(Go go) throws IOException {
		out.write("go ");
		go.getExpression().accept(new GoExpressionFormattingVisitor(out));
		return null;
	}
}
