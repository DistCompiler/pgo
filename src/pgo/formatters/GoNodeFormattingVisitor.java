package pgo.formatters;

import java.io.IOException;

import pgo.model.golang.Declaration;
import pgo.model.golang.Expression;
import pgo.model.golang.FunctionArgument;
import pgo.model.golang.InterfaceTypeField;
import pgo.model.golang.LabelName;
import pgo.model.golang.Module;
import pgo.model.golang.NodeVisitor;
import pgo.model.golang.Statement;
import pgo.model.golang.StructTypeField;
import pgo.model.golang.SwitchCase;
import pgo.model.golang.Type;

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
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(SwitchCase switchCase) throws IOException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(LabelName labelName) throws IOException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(FunctionArgument functionArgument) throws IOException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Void visit(Expression expression) throws IOException {
		expression.accept(new GoExpressionFormattingVisitor(out));
		return null;
	}

	@Override
	public Void visit(InterfaceTypeField interfaceTypeField) throws IOException {
		throw new RuntimeException("TODO");
	}

}
