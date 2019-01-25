package pgo.trans.passes.scope;

import pgo.TODO;
import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;
import pgo.trans.passes.scope.TLAScopeBuilder;

import java.util.List;

public class PlusCalStatementLabelCaptureVisitor extends PlusCalStatementVisitor<Void, RuntimeException> {
	IssueContext ctx;
	TLAScopeBuilder builder;

	public PlusCalStatementLabelCaptureVisitor(IssueContext ctx, TLAScopeBuilder builder) {
		this.ctx = ctx;
		this.builder = builder;
	}

	@Override
	public Void visit(PlusCalLabeledStatements plusCalLabeledStatements) throws RuntimeException {
		String name = plusCalLabeledStatements.getLabel().getName();
		PlusCalLabel label = plusCalLabeledStatements.getLabel();
		builder.declare(name, label.getUID());

		for(PlusCalStatement stmt : plusCalLabeledStatements.getStatements()) {
			stmt.accept(this);
		}

		return null;
	}

	@Override
	public Void visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		for(PlusCalStatement stmt : plusCalWhile.getBody()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalIf plusCalIf) throws RuntimeException {
		for(PlusCalStatement stmt : plusCalIf.getYes()) {
			stmt.accept(this);
		}
		for(PlusCalStatement stmt : plusCalIf.getNo()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalEither plusCalEither) throws RuntimeException {
		for(List<PlusCalStatement> list : plusCalEither.getCases()) {
			for(PlusCalStatement stmt : list) {
				stmt.accept(this);
			}
		}
		return null;
	}

	@Override
	public Void visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		return null;
	}

	@Override
	public Void visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		return null;
	}

	@Override
	public Void visit(PlusCalSkip plusCalSkip) throws RuntimeException {
		return null;
	}

	@Override
	public Void visit(PlusCalCall plusCalCall) throws RuntimeException {
		return null;
	}

	@Override
	public Void visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(PlusCalWith plusCalWith) throws RuntimeException {
		for(PlusCalStatement stmt : plusCalWith.getBody()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		return null;
	}

	@Override
	public Void visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		return null;
	}

	@Override
	public Void visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		return null;
	}

	@Override
	public Void visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		return null;
	}

	@Override
	public Void visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		throw new TODO();
	}
}
