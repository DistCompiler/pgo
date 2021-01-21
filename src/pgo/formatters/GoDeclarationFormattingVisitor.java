package pgo.formatters;

import pgo.TODO;
import pgo.model.golang.GoDeclarationVisitor;
import pgo.model.golang.GoFunctionDeclaration;
import pgo.model.golang.GoTypeDeclaration;
import pgo.model.golang.GoVariableDeclaration;

import java.io.IOException;

public class GoDeclarationFormattingVisitor extends GoDeclarationVisitor<Void, IOException> {

	private final IndentingWriter out;

	public GoDeclarationFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(GoFunctionDeclaration functionDeclaration) throws IOException {
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
	public Void visit(GoTypeDeclaration typeDeclaration) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(GoVariableDeclaration variableDeclaration) throws IOException {
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
