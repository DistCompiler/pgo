package pgo.trans.intermediate;

import java.util.List;

import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.pcal.*;
import pgo.model.pcal.PlusCalAssert;

public class PlusCalStatementLabelCaptureVisitor extends PlusCalStatementVisitor<Void, RuntimeException> {

	IssueContext ctx;
	TLAScopeBuilder builder;

	public PlusCalStatementLabelCaptureVisitor(IssueContext ctx, TLAScopeBuilder builder) {
		this.ctx = ctx;
		this.builder = builder;
	}

	@Override
	public Void visit(PlusCalLabeledStatements labeledStatements) throws RuntimeException {
		String name = labeledStatements.getLabel().getName();
		PlusCalLabel label = labeledStatements.getLabel();
		builder.declare(name, label.getUID());

		for(PlusCalStatement stmt : labeledStatements.getStatements()) {
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
	public Void visit(PlusCalSkip skip) throws RuntimeException {
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
	public Void visit(PlusCalWith with) throws RuntimeException {
		for(PlusCalStatement stmt : with.getBody()) {
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

}
