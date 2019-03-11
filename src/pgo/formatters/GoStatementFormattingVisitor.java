package pgo.formatters;

import pgo.TODO;
import pgo.model.golang.*;

import java.io.IOException;
import java.util.List;

public class GoStatementFormattingVisitor extends GoStatementVisitor<Void, IOException> {

	private IndentingWriter out;

	public GoStatementFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(GoComment comment) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(GoAssignmentStatement assignment) throws IOException {
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
	public Void visit(GoReturn goReturn) throws IOException {
		out.write("return");
		List<GoExpression> expressions = goReturn.getValues();
		if (expressions.size() == 0) {
			return null;
		}
		out.write(" ");
		FormattingTools.writeCommaSeparated(out, expressions, e -> e.accept(new GoExpressionFormattingVisitor(out)));
		return null;
	}

	@Override
	public Void visit(GoBlock block) throws IOException {
		out.write("{");
		out.newLine();
		try (IndentingWriter.Indent ignored = out.indent()) {
			for (GoStatement stmt : block.getStatements()) {
				stmt.accept(this);
				out.newLine();
			}
		}
		out.write("}");
		return null;
	}

	@Override
	public Void visit(GoFor goFor) throws IOException {
		out.write("for ");
		if (goFor.getInit() != null) {
			goFor.getInit().accept(this);
			out.write("; ");
		}
		if (goFor.getCondition() != null) {
			goFor.getCondition().accept(new GoExpressionFormattingVisitor(out));
		}
		if (goFor.getIncrement() != null) {
			out.write("; ");
			goFor.getIncrement().accept(this);
		}
		if (goFor.getCondition() != null) {
			out.write(" ");
		}
		goFor.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(GoForRange forRange) throws IOException {
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
	public Void visit(GoIf goIf) throws IOException {
		out.write("if ");
		if (goIf.getInitialExpression() != null) {
			FormattingTools.writeCommaSeparated(
					out,
					goIf.getInitialVariables(),
					e -> e.accept(new GoExpressionFormattingVisitor(out))
			);
			out.write(" := ");
			goIf.getInitialExpression().accept(new GoExpressionFormattingVisitor(out));
			out.write("; ");
		}

		goIf.getCond().accept(new GoExpressionFormattingVisitor(out));
		out.write(" ");
		goIf.getThen().accept(this);
		if (goIf.getElse() != null && !goIf.getElse().getStatements().isEmpty()) {
			out.write(" else ");
			goIf.getElse().accept(this);
		}
		return null;
	}

	@Override
	public Void visit(GoSwitch goSwitch) throws IOException {
		out.write("switch ");
		if (goSwitch.getCondition() != null) {
			goSwitch.getCondition().accept(new GoExpressionFormattingVisitor(out));
		}
		out.write(" {");
		out.newLine();
		for (GoSwitchCase switchCase : goSwitch.getCases()) {
			out.write("case ");
			switchCase.getCondition().accept(new GoExpressionFormattingVisitor(out));
			out.write(":");
			out.newLine();
			for (GoStatement statement : switchCase.getBlock()) {
				statement.accept(this);
				out.newLine();
			}
		}
		if (goSwitch.getDefaultBlock() != null) {
			out.write("default:");
			for (GoStatement statement : goSwitch.getDefaultBlock()) {
				statement.accept(this);
				out.newLine();
			}
		}
		out.write("}");
		return null;
	}

	@Override
	public Void visit(GoLabel label) throws IOException {
		out.write(label.getName());
		out.write(":");
		return null;
	}

	@Override
	public Void visit(GoSelect select) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(GoTo goTo) throws IOException {
		out.write("goto ");
		out.write(goTo.getTo().getName());
		return null;
	}

	@Override
	public Void visit(GoIncDec incDec) throws IOException {
		incDec.getExpression().accept(new GoExpressionFormattingVisitor(out));
		if (incDec.isInc()) {
			out.write("++");
		} else {
			out.write("--");
		}
		return null;
	}

	@Override
	public Void visit(GoExpressionStatement expressionStatement) throws IOException {
		expressionStatement.getExpression().accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoBreak break1) throws IOException {
		out.write("break");
		return null;
	}

	@Override
	public Void visit(GoContinue continue1) throws IOException {
		out.write("continue");
		return null;
	}

	@Override
	public Void visit(GoDefer defer) throws IOException {
		out.write("defer ");
		defer.getExpression().accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoRoutineStatement go) throws IOException {
		out.write("go ");
		go.getExpression().accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoVariableDeclarationStatement variableDeclarationStatement) throws IOException {
		GoVariableDeclaration variableDeclaration = variableDeclarationStatement.getVariableDeclaration();
		out.write("var ");
		out.write(variableDeclaration.getName());
		out.write(" ");
		variableDeclaration.getType().accept(new GoTypeFormattingVisitor(out));
		if (variableDeclaration.getValue() != null) {
			out.write(" = ");
			variableDeclaration.getValue().accept(new GoExpressionFormattingVisitor(out));
		}
		return null;
	}
}
