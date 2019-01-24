package pgo.formatters;

import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.golang.type.GoInterfaceTypeField;
import pgo.model.golang.type.GoStructTypeField;
import pgo.model.golang.type.GoType;

import java.io.IOException;

public class GoNodeFormattingVisitor extends GoNodeVisitor<Void, IOException> {

	private IndentingWriter out;

	public GoNodeFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(GoModule module) throws IOException {
		out.write("package ");
		module.getPackage().accept(new GoExpressionFormattingVisitor(out));
		out.newLine();
		out.newLine();
		if(!module.getImports().isEmpty()) {
			out.write("import (");
			out.newLine();
			try(IndentingWriter.Indent i_ = out.indent()){
				for(String imp : module.getImports()) {
					out.write("\"");
					out.write(imp); // TODO: escaping
					out.write("\"");
					out.newLine();
				}
			}
			out.write(")");
			out.newLine();
		}
		out.newLine();
		for(GoDeclaration decl : module.getDeclarations()) {
			decl.accept(this);
			out.newLine();
			out.newLine();
		}
		return null;
	}

	@Override
	public Void visit(GoStatement statement) throws IOException {
		statement.accept(new GoStatementFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoDeclaration declaration) throws IOException {
		declaration.accept(new GoDeclarationFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoType type) throws IOException {
		type.accept(new GoTypeFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoStructTypeField structTypeField) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(GoSwitchCase switchCase) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(GoLabelName labelName) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(GoFunctionParameter functionArgument) throws IOException {
		if (functionArgument.getName() != null) {
			out.write(functionArgument.getName());
			out.write(" ");
		}
		functionArgument.getType().accept(this);
		return null;
	}

	@Override
	public Void visit(GoExpression expression) throws IOException {
		expression.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(GoInterfaceTypeField interfaceTypeField) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(GoSelectCase selectCase) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(GoStructLiteralField structLiteralField) throws IOException {
		if(structLiteralField.getName() != null){
			out.write(structLiteralField.getName());
			out.write(": ");
		}
		structLiteralField.getValue().accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

}
