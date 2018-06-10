package pgo.formatters;

import java.io.IOException;

import pgo.TODO;
import pgo.model.golang.*;

public class GoNodeFormattingVisitor extends NodeVisitor<Void, IOException> {

	private IndentingWriter out;

	public GoNodeFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(Module module) throws IOException {
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
		for(Declaration decl : module.getDeclarations()) {
			decl.accept(this);
			out.newLine();
			out.newLine();
		}
		return null;
	}

	@Override
	public Void visit(Statement statement) throws IOException {
		statement.accept(new GoStatementFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(Declaration declaration) throws IOException {
		declaration.accept(new GoDeclarationFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(Type type) throws IOException {
		type.accept(new GoTypeFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(StructTypeField structTypeField) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(SwitchCase switchCase) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(LabelName labelName) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(FunctionArgument functionArgument) throws IOException {
		if (functionArgument.getName() != null) {
			out.write(functionArgument.getName());
			out.write(" ");
		}
		functionArgument.getType().accept(this);
		return null;
	}

	@Override
	public Void visit(Expression expression) throws IOException {
		expression.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(InterfaceTypeField interfaceTypeField) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(SelectCase selectCase) throws IOException {
		throw new TODO();
	}

	@Override
	public Void visit(StructLiteralField structLiteralField) throws IOException {
		if(structLiteralField.getName() != null){
			out.write(structLiteralField.getName());
			out.write(": ");
		}
		structLiteralField.getValue().accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

}
