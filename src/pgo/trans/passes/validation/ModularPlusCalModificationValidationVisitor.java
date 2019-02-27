package pgo.trans.passes.validation;

import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.List;
import java.util.Set;

public class ModularPlusCalModificationValidationVisitor extends PlusCalStatementVisitor<Void, RuntimeException> {
	private final TLAExpressionLHSModificationValidationVisitor lhsVisitor;

	public ModularPlusCalModificationValidationVisitor(IssueContext ctx, DefinitionRegistry registry,
	                                                   Set<UID> nonRefParams) {
		this.lhsVisitor = new TLAExpressionLHSModificationValidationVisitor(ctx, registry, nonRefParams);
	}

	@Override
	public Void visit(PlusCalLabeledStatements plusCalLabeledStatements) throws RuntimeException {
		for (PlusCalStatement statement : plusCalLabeledStatements.getStatements()) {
			statement.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		for (PlusCalStatement statement : plusCalWhile.getBody()) {
			statement.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalIf plusCalIf) throws RuntimeException {
		for (PlusCalStatement statement : plusCalIf.getYes()) {
			statement.accept(this);
		}
		for (PlusCalStatement statement : plusCalIf.getNo()) {
			statement.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalEither plusCalEither) throws RuntimeException {
		for (List<PlusCalStatement> aCase : plusCalEither.getCases()) {
			for (PlusCalStatement statement : aCase) {
				statement.accept(this);
			}
		}
		return null;
	}

	@Override
	public Void visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		for (PlusCalAssignmentPair pair : plusCalAssignment.getPairs()) {
			pair.getLhs().accept(lhsVisitor);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalSkip plusCalSkip) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalCall plusCalCall) throws RuntimeException {
		// TODO
		return null;
	}

	@Override
	public Void visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(PlusCalWith plusCalWith) throws RuntimeException {
		for (PlusCalStatement statement : plusCalWith.getBody()) {
			statement.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		throw new Unreachable();
	}
}
