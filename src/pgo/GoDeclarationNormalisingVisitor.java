package pgo;

import pgo.model.golang.Declaration;
import pgo.model.golang.DeclarationVisitor;
import pgo.model.golang.FunctionDeclaration;
import pgo.model.golang.TypeDeclaration;
import pgo.model.golang.VariableDeclaration;

public class GoDeclarationNormalisingVisitor extends DeclarationVisitor<Declaration, RuntimeException> {

	@Override
	public Declaration visit(FunctionDeclaration functionDeclaration) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Declaration visit(TypeDeclaration typeDeclaration) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Declaration visit(VariableDeclaration variableDeclaration) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

}
