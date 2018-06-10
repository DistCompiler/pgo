package pgo.formatters;

import java.io.IOException;

import pgo.TODO;
import pgo.model.golang.DeclarationVisitor;
import pgo.model.golang.FunctionDeclaration;
import pgo.model.golang.TypeDeclaration;
import pgo.model.golang.VariableDeclaration;

public class GoDeclarationFormattingVisitor extends DeclarationVisitor<Void, IOException> {

	private IndentingWriter out;

	public GoDeclarationFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(FunctionDeclaration functionDeclaration) throws IOException {
		out.write("func ");
		if(functionDeclaration.getReceiver() != null) {
			out.write("(");
			functionDeclaration.getReceiver().accept(new GoNodeFormattingVisitor(out));
			out.write(") ");
		}
		out.write(functionDeclaration.getName());
		out.write("(");
		FormattingTools.writeCommaSeparated(out, functionDeclaration.getArguments(), arg -> {
			arg.accept(new GoNodeFormattingVisitor(out));
		});
		out.write(") ");
		if(!functionDeclaration.getReturnTypes().isEmpty()) {
			out.write("(");
			FormattingTools.writeCommaSeparated(out, functionDeclaration.getReturnTypes(), ret -> {
				ret.accept(new GoNodeFormattingVisitor(out));
			});
			out.write(") ");
		}
		functionDeclaration.getBody().accept(new GoStatementFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(TypeDeclaration typeDeclaration) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(VariableDeclaration variableDeclaration) throws IOException {
		out.write("var ");
		out.write(variableDeclaration.getName());
		if(variableDeclaration.getType() != null) {
			out.write(" ");
			variableDeclaration.getType().accept(new GoTypeFormattingVisitor(out));
		}
		if(variableDeclaration.getValue() != null) {
			out.write(" = ");
			variableDeclaration.getValue().accept(new GoExpressionFormattingVisitor(out));
		}
		return null;
	}

}
