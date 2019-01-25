package pgo.trans.passes.validation;

import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;

import java.util.List;

public class NonModularPlusCalStatementValidationVisitor extends PlusCalStatementVisitor<Boolean, RuntimeException> {
	private final NonModularPlusCalTLAExpressionValidationVisitor visitor;

	public NonModularPlusCalStatementValidationVisitor() {
		this.visitor = new NonModularPlusCalTLAExpressionValidationVisitor();
	}

	boolean validateStatements(List<PlusCalStatement> statements) {
		return statements.stream().allMatch(s -> s.accept(this));
	}

	boolean validateDeclarations(List<PlusCalVariableDeclaration> declarations) {
		return declarations.stream().allMatch(d -> !d.isRef() && d.getValue().accept(visitor));
	}

	@Override
	public Boolean visit(PlusCalLabeledStatements plusCalLabeledStatements) throws RuntimeException {
		return validateStatements(plusCalLabeledStatements.getStatements());
	}

	@Override
	public Boolean visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		return plusCalWhile.getCondition().accept(visitor) && validateStatements(plusCalWhile.getBody());
	}

	@Override
	public Boolean visit(PlusCalIf plusCalIf) throws RuntimeException {
		return plusCalIf.getCondition().accept(visitor) &&
				validateStatements(plusCalIf.getYes()) &&
				validateStatements(plusCalIf.getNo());
	}

	@Override
	public Boolean visit(PlusCalEither plusCalEither) throws RuntimeException {
		return plusCalEither.getCases().stream().allMatch(this::validateStatements);
	}

	@Override
	public Boolean visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		return plusCalAssignment
				.getPairs()
				.stream()
				.allMatch(p -> p.getLhs().accept(visitor) && p.getRhs().accept(visitor));
	}

	@Override
	public Boolean visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(PlusCalSkip plusCalSkip) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(PlusCalCall plusCalCall) throws RuntimeException {
		return plusCalCall.getArguments().stream().allMatch(a -> a.accept(visitor));
	}

	@Override
	public Boolean visit(PlusCalMacroCall macroCall) throws RuntimeException {
		return macroCall.getArguments().stream().allMatch(a -> a.accept(visitor));
	}

	@Override
	public Boolean visit(PlusCalWith plusCalWith) throws RuntimeException {
		return validateDeclarations(plusCalWith.getVariables()) && validateStatements(plusCalWith.getBody());
	}

	@Override
	public Boolean visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		return plusCalPrint.getValue().accept(visitor);
	}

	@Override
	public Boolean visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		return plusCalAssert.getCondition().accept(visitor);
	}

	@Override
	public Boolean visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		return plusCalAwait.getCondition().accept(visitor);
	}

	@Override
	public Boolean visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		return false;
	}
}
