package pgo.trans.passes.validation;

import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;
import pgo.trans.intermediate.DanglingReferenceIssue;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Stream;

public class StatementVariableAccessValidationVisitor extends PlusCalStatementVisitor<Void, RuntimeException> {
	private final IssueContext ctx;
	private final Set<String> macrosInScope;
	private final Set<String> proceduresInScope;
	private final Set<String> variablesInScope;
	private final Set<String> refVariablesInScope;
	private final ExpressionVariableAccessValidationVisitor visitor;

	public StatementVariableAccessValidationVisitor(IssueContext ctx, Set<String> macrosInScope,
	                                                Set<String> proceduresInScope, Set<String> variablesInScope,
	                                                Set<String> refVariablesInScope) {
		this.ctx = ctx;
		this.macrosInScope = macrosInScope;
		this.proceduresInScope = proceduresInScope;
		this.variablesInScope = variablesInScope;
		this.refVariablesInScope = refVariablesInScope;
		this.visitor = new ExpressionVariableAccessValidationVisitor(
				ctx, macrosInScope, proceduresInScope, variablesInScope, refVariablesInScope);
	}

	public static void validateDeclarations(IssueContext ctx, Set<String> localMacrosInScope,
	                                        Set<String> localProceduresInScope, Set<String> localVariablesInScope,
	                                        Set<String> localRefVariablesInScope,
	                                        Stream<PlusCalVariableDeclaration> declarationStream) {
		declarationStream.forEach(declaration -> {
			String name = declaration.getName().getValue();
			if (declaration.isRef()) {
				localRefVariablesInScope.add(name);
				localVariablesInScope.remove(name);
			} else {
				localVariablesInScope.add(name);
				localRefVariablesInScope.remove(name);
			}
			localMacrosInScope.remove(name);
			localProceduresInScope.remove(name);
			declaration.getValue().accept(new ExpressionVariableAccessValidationVisitor(
					ctx, localMacrosInScope, localProceduresInScope, localVariablesInScope, localRefVariablesInScope));
		});
	}

	@Override
	public Void visit(PlusCalLabeledStatements labeledStatements) throws RuntimeException {
		labeledStatements.getStatements().forEach(s -> s.accept(this));
		return null;
	}

	@Override
	public Void visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		plusCalWhile.getCondition().accept(visitor);
		plusCalWhile.getBody().forEach(s -> s.accept(this));
		return null;
	}

	@Override
	public Void visit(PlusCalIf plusCalIf) throws RuntimeException {
		plusCalIf.getCondition().accept(visitor);
		plusCalIf.getYes().forEach(s -> s.accept(this));
		plusCalIf.getNo().forEach(s -> s.accept(this));
		return null;
	}

	@Override
	public Void visit(PlusCalEither plusCalEither) throws RuntimeException {
		plusCalEither.getCases().forEach(c -> c.forEach(s -> s.accept(this)));
		return null;
	}

	@Override
	public Void visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		plusCalAssignment.getPairs().forEach(p -> {
			p.getLhs().accept(visitor);
			p.getRhs().accept(visitor);
		});
		return null;
	}

	@Override
	public Void visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalSkip skip) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalCall plusCalCall) throws RuntimeException {
		if (!proceduresInScope.contains(plusCalCall.getTarget())) {
			ctx.error(new DanglingReferenceIssue(plusCalCall.getUID()));
		}
		plusCalCall.getArguments().forEach(e -> e.accept(visitor));
		return null;
	}

	@Override
	public Void visit(PlusCalMacroCall macroCall) throws RuntimeException {
		if (!macrosInScope.contains(macroCall.getTarget())) {
			ctx.error(new DanglingReferenceIssue(macroCall.getUID()));
		}
		macroCall.getArguments().forEach(e -> e.accept(visitor));
		return null;
	}

	@Override
	public Void visit(PlusCalWith with) throws RuntimeException {
		Set<String> localVariablesInScope = new HashSet<>(variablesInScope);
		Set<String> localRefVariablesInScope = new HashSet<>(refVariablesInScope);
		Set<String> localMacrosInScope = new HashSet<>(macrosInScope);
		Set<String> localProceduresInScope = new HashSet<>(proceduresInScope);
		validateDeclarations(
				ctx, localMacrosInScope, localProceduresInScope, localVariablesInScope, localRefVariablesInScope, with.getVariables().stream());
		with.getBody().forEach(s -> s.accept(new StatementVariableAccessValidationVisitor(
				ctx, localMacrosInScope, localProceduresInScope, localVariablesInScope, localRefVariablesInScope)));
		return null;
	}

	@Override
	public Void visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		plusCalPrint.getValue().accept(visitor);
		return null;
	}

	@Override
	public Void visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		plusCalAssert.getCondition().accept(visitor);
		return null;
	}

	@Override
	public Void visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		plusCalAwait.getCondition().accept(visitor);
		return null;
	}

	@Override
	public Void visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		modularPlusCalYield.getExpression().accept(visitor);
		return null;
	}
}
