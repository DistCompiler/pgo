package pgo.formatters;

import pgo.TODO;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;

import java.io.IOException;
import java.util.List;

public class PlusCalStatementFormattingVisitor extends PlusCalStatementVisitor<Void, IOException> {
	private final IndentingWriter out;

	public PlusCalStatementFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(PlusCalLabeledStatements plusCalLabeledStatements) throws IOException {
		plusCalLabeledStatements.getLabel().accept(new PlusCalNodeFormattingVisitor(out));
		try (IndentingWriter.Indent ignored = out.indent()) {
			for(PlusCalStatement stmt : plusCalLabeledStatements.getStatements()) {
				out.newLine();
				stmt.accept(this);
			}
		}
		out.newLine();
		return null;
	}

	@Override
	public Void visit(PlusCalWhile plusCalWhile) throws IOException {
		out.write("while (");
		plusCalWhile.getCondition().accept(new TLAExpressionFormattingVisitor(out));
		out.write(") {");
		try (IndentingWriter.Indent ignored = out.indent()) {
			for(PlusCalStatement stmt : plusCalWhile.getBody()) {
				out.newLine();
				stmt.accept(this);
			}
		}
		out.newLine();
		out.write("};");
		return null;
	}

	@Override
	public Void visit(PlusCalIf plusCalIf) throws IOException {
		out.write("if (");
		plusCalIf.getCondition().accept(new TLAExpressionFormattingVisitor(out));
		out.write(") {");
		try (IndentingWriter.Indent ignored = out.indent()) {
			for(PlusCalStatement stmt : plusCalIf.getYes()){
				out.newLine();
				stmt.accept(new PlusCalStatementFormattingVisitor(out));
			}
		}
		out.newLine();
		out.write("}");
		if (!plusCalIf.getNo().isEmpty()) {
			out.write(" else {");
			try (IndentingWriter.Indent ignored = out.indent()) {
				for(PlusCalStatement stmt : plusCalIf.getNo()){
					out.newLine();
					stmt.accept(new PlusCalStatementFormattingVisitor(out));
				}
			}
			out.newLine();
			out.write("}");
		}
		return null;
	}

	@Override
	public Void visit(PlusCalEither plusCalEither) throws IOException {
		List<List<PlusCalStatement>> cases = plusCalEither.getCases();
		for (int i = 0; i < cases.size(); i++) {
			List<PlusCalStatement> case_ = cases.get(i);
			if (i == 0) {
				out.write("either {");
			} else {
				out.write(" or {");
			}
			try (IndentingWriter.Indent ignored = out.indent()) {
				for (PlusCalStatement statement : case_) {
					out.newLine();
					statement.accept(this);
				}
			}
			out.newLine();
			out.write("}");
		}
		return null;
	}

	@Override
	public Void visit(PlusCalAssignment plusCalAssignment) throws IOException {
		List<PlusCalAssignmentPair> pairs = plusCalAssignment.getPairs();

		pairs.get(0).accept(new PlusCalNodeFormattingVisitor(out));

		for(PlusCalAssignmentPair pair : pairs.subList(1, pairs.size())) {
			out.write(" || ");
			pair.accept(new PlusCalNodeFormattingVisitor(out));
		}
		out.write(";");
		return null;
	}

	@Override
	public Void visit(PlusCalReturn plusCalReturn) throws IOException {
		out.write("return;");
		return null;
	}

	@Override
	public Void visit(PlusCalSkip plusCalSkip) throws IOException {
		out.write("skip;");
		return null;
	}

	@Override
	public Void visit(PlusCalCall plusCalCall) throws IOException {
		out.write("call ");
		out.write(plusCalCall.getTarget());
		out.write("(");

		for (TLAExpression arg : plusCalCall.getArguments()) {
			arg.accept(new TLANodeFormattingVisitor(out));
		}

		out.write(");");
		return null;
	}

	@Override
	public Void visit(PlusCalMacroCall macroCall) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(PlusCalWith plusCalWith) throws IOException {
		out.write("with (");
		(new PlusCalNodeFormattingVisitor(out)).writeVariableDeclarations("", plusCalWith.getVariables(), "");
		out.write(") {");
		out.newLine();
		try (IndentingWriter.Indent ignored = out.indent()) {
			for (PlusCalStatement statement : plusCalWith.getBody()) {
				statement.accept(this);
				out.newLine();
			}
		}
		out.write("};");
		return null;
	}

	@Override
	public Void visit(PlusCalPrint plusCalPrint) throws IOException {
		out.write("print ");
		plusCalPrint.getValue().accept(new TLAExpressionFormattingVisitor(out));
		out.write(";");
		return null;
	}

	@Override
	public Void visit(PlusCalAssert plusCalAssert) throws IOException {
		out.write("assert ");
		plusCalAssert.getCondition().accept(new TLAExpressionFormattingVisitor(out));
		out.write(";");
		return null;
	}

	@Override
	public Void visit(PlusCalAwait plusCalAwait) throws IOException {
		out.write("await ");
		plusCalAwait.getCondition().accept(new TLAExpressionFormattingVisitor(out));
		out.write(";");
		return null;
	}

	@Override
	public Void visit(PlusCalGoto plusCalGoto) throws IOException {
		out.write("goto " + plusCalGoto.getTarget() + ";");
		return null;
	}

	@Override
	public Void visit(ModularPlusCalYield modularPlusCalYield) throws IOException {
		out.write("yield ");
		modularPlusCalYield.getExpression().accept(new TLAExpressionFormattingVisitor(out));
		out.write(";");
		return null;
	}
}
