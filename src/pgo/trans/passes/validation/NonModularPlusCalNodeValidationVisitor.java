package pgo.trans.passes.validation;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.pcal.*;

import java.util.List;

public class NonModularPlusCalNodeValidationVisitor extends PlusCalNodeVisitor<Boolean, RuntimeException> {
	private final NonModularPlusCalStatementValidationVisitor statementVisitor;
	private final NonModularPlusCalTLAExpressionValidationVisitor expressionVisitor;

	public NonModularPlusCalNodeValidationVisitor() {
		this.statementVisitor = new NonModularPlusCalStatementValidationVisitor();
		this.expressionVisitor = new NonModularPlusCalTLAExpressionValidationVisitor();
	}

	private boolean validateStatements(List<PlusCalStatement> statements) {
		return statements.stream().allMatch(s -> s.accept(statementVisitor));
	}

	@Override
	public Boolean visit(PlusCalAlgorithm plusCalAlgorithm) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Boolean visit(PlusCalProcesses processes) throws RuntimeException {
		if (processes instanceof PlusCalSingleProcess) {
			return statementVisitor.validateStatements(((PlusCalSingleProcess) processes).getBody());
		}
		if (processes instanceof PlusCalMultiProcess) {
			return ((PlusCalMultiProcess) processes).getProcesses().stream().allMatch(p -> p.accept(this));
		}
		throw new Unreachable();
	}

	@Override
	public Boolean visit(PlusCalStatement statement) throws RuntimeException {
		return statement.accept(statementVisitor);
	}

	@Override
	public Boolean visit(PlusCalLabel label) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(PlusCalMacro macro) throws RuntimeException {
		return validateStatements(macro.getBody());
	}

	@Override
	public Boolean visit(PlusCalProcess plusCalProcess) throws RuntimeException {
		return plusCalProcess.getName().accept(this) &&
				statementVisitor.validateDeclarations(plusCalProcess.getVariables()) &&
				statementVisitor.validateStatements(plusCalProcess.getBody());
	}

	@Override
	public Boolean visit(PlusCalProcedure procedure) throws RuntimeException {
		return statementVisitor.validateDeclarations(procedure.getParams()) &&
				statementVisitor.validateDeclarations(procedure.getVariables()) &&
				statementVisitor.validateStatements(procedure.getBody());
	}

	@Override
	public Boolean visit(PlusCalVariableDeclaration variableDeclaration) throws RuntimeException {
		return !variableDeclaration.isRef() && variableDeclaration.getValue().accept(expressionVisitor);
	}

	@Override
	public Boolean visit(PlusCalAssignmentPair plusCalAssignmentPair) throws RuntimeException {
		return plusCalAssignmentPair.getLhs().accept(expressionVisitor) &&
				plusCalAssignmentPair.getRhs().accept(expressionVisitor);
	}
}

