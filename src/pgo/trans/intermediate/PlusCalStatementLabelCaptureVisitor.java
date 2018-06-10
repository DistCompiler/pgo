package pgo.trans.intermediate;

import java.util.List;

import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.pcal.Assert;
import pgo.model.pcal.Assignment;
import pgo.model.pcal.Await;
import pgo.model.pcal.Call;
import pgo.model.pcal.Either;
import pgo.model.pcal.Goto;
import pgo.model.pcal.If;
import pgo.model.pcal.Label;
import pgo.model.pcal.LabeledStatements;
import pgo.model.pcal.MacroCall;
import pgo.model.pcal.Print;
import pgo.model.pcal.Return;
import pgo.model.pcal.Skip;
import pgo.model.pcal.Statement;
import pgo.model.pcal.StatementVisitor;
import pgo.model.pcal.While;
import pgo.model.pcal.With;

public class PlusCalStatementLabelCaptureVisitor extends StatementVisitor<Void, RuntimeException> {

	IssueContext ctx;
	TLAScopeBuilder builder;

	public PlusCalStatementLabelCaptureVisitor(IssueContext ctx, TLAScopeBuilder builder) {
		this.ctx = ctx;
		this.builder = builder;
	}

	@Override
	public Void visit(LabeledStatements labeledStatements) throws RuntimeException {
		String name = labeledStatements.getLabel().getName();
		Label label = labeledStatements.getLabel();
		builder.declare(name, label.getUID());

		for(Statement stmt : labeledStatements.getStatements()) {
			stmt.accept(this);
		}

		return null;
	}

	@Override
	public Void visit(While while1) throws RuntimeException {
		for(Statement stmt : while1.getBody()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(If if1) throws RuntimeException {
		for(Statement stmt : if1.getYes()) {
			stmt.accept(this);
		}
		for(Statement stmt : if1.getNo()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(Either either) throws RuntimeException {
		for(List<Statement> list : either.getCases()) {
			for(Statement stmt : list) {
				stmt.accept(this);
			}
		}
		return null;
	}

	@Override
	public Void visit(Assignment assignment) throws RuntimeException {
		return null;
	}

	@Override
	public Void visit(Return return1) throws RuntimeException {
		return null;
	}

	@Override
	public Void visit(Skip skip) throws RuntimeException {
		return null;
	}

	@Override
	public Void visit(Call call) throws RuntimeException {
		return null;
	}

	@Override
	public Void visit(MacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(With with) throws RuntimeException {
		for(Statement stmt : with.getBody()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(Print print) throws RuntimeException {
		return null;
	}

	@Override
	public Void visit(Assert assert1) throws RuntimeException {
		return null;
	}

	@Override
	public Void visit(Await await) throws RuntimeException {
		return null;
	}

	@Override
	public Void visit(Goto goto1) throws RuntimeException {
		return null;
	}

}
