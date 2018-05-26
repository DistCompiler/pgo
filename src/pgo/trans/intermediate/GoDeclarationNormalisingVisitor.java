package pgo.trans.intermediate;

import java.util.Set;

import pgo.model.golang.Block;
import pgo.model.golang.Declaration;
import pgo.model.golang.DeclarationVisitor;
import pgo.model.golang.FunctionDeclaration;
import pgo.model.golang.TypeDeclaration;
import pgo.model.golang.VariableDeclaration;

public class GoDeclarationNormalisingVisitor extends DeclarationVisitor<Declaration, RuntimeException> {

	@Override
	public Declaration visit(FunctionDeclaration functionDeclaration) throws RuntimeException {
		Set<String> usedLabels = functionDeclaration.getBody().accept(new GoStatementFindUsedLabelsVisitor());
		Block body = (Block)functionDeclaration.getBody().accept(new GoStatementRemoveUnusedLabelsVisitor(usedLabels));
		return new FunctionDeclaration(
				functionDeclaration.getName(),
				functionDeclaration.getReceiver(),
				functionDeclaration.getArguments(),
				functionDeclaration.getReturnTypes(),
				body);
	}

	@Override
	public Declaration visit(TypeDeclaration typeDeclaration) throws RuntimeException {
		return typeDeclaration;
	}

	@Override
	public Declaration visit(VariableDeclaration variableDeclaration) throws RuntimeException {
		return variableDeclaration;
	}

}
