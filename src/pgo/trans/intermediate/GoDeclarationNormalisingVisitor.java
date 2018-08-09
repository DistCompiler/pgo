package pgo.trans.intermediate;

import java.util.Set;

import pgo.model.golang.*;
import pgo.model.golang.GoDeclaration;

public class GoDeclarationNormalisingVisitor extends GoDeclarationVisitor<GoDeclaration, RuntimeException> {

	@Override
	public GoDeclaration visit(GoFunctionDeclaration functionDeclaration) throws RuntimeException {
		Set<String> usedLabels = functionDeclaration.getBody().accept(new GoStatementFindUsedLabelsVisitor());
		GoBlock body = (GoBlock)functionDeclaration.getBody().accept(new GoStatementRemoveUnusedLabelsVisitor(usedLabels));
		return new GoFunctionDeclaration(
				functionDeclaration.getName(),
				functionDeclaration.getReceiver(),
				functionDeclaration.getArguments(),
				functionDeclaration.getReturnTypes(),
				body);
	}

	@Override
	public GoDeclaration visit(GoTypeDeclaration typeDeclaration) throws RuntimeException {
		return typeDeclaration;
	}

	@Override
	public GoDeclaration visit(GoVariableDeclaration variableDeclaration) throws RuntimeException {
		return variableDeclaration;
	}

}
