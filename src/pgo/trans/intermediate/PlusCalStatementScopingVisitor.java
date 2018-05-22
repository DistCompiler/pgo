package pgo.trans.intermediate;

import java.util.List;

import pgo.errors.IssueContext;
import pgo.model.pcal.Assert;
import pgo.model.pcal.Assignment;
import pgo.model.pcal.Await;
import pgo.model.pcal.Call;
import pgo.model.pcal.Either;
import pgo.model.pcal.Goto;
import pgo.model.pcal.If;
import pgo.model.pcal.LabeledStatements;
import pgo.model.pcal.MacroCall;
import pgo.model.pcal.Print;
import pgo.model.pcal.Return;
import pgo.model.pcal.Skip;
import pgo.model.pcal.Statement;
import pgo.model.pcal.StatementVisitor;
import pgo.model.pcal.While;
import pgo.model.pcal.With;
import pgo.model.tla.PGoTLAExpression;

public class PlusCalStatementScopingVisitor extends StatementVisitor<Void, RuntimeException> {
	
	IssueContext ctx;
	TLAScopeBuilder builder;
	
	public PlusCalStatementScopingVisitor(IssueContext ctx, TLAScopeBuilder builder) {
		this.ctx = ctx;
		this.builder = builder;
	}

	@Override
	public Void visit(LabeledStatements labeledStatements) throws RuntimeException {
		for(Statement stmt : labeledStatements.getStatements()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(While while1) throws RuntimeException {
		while1.getCondition().accept(new TLAExpressionScopingVisitor(builder));
		for(Statement stmt : while1.getBody()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(If if1) throws RuntimeException {
		if1.getCondition().accept(new TLAExpressionScopingVisitor(builder));
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
		assignment.getLHS().accept(new TLAExpressionScopingVisitor(builder));
		assignment.getRHS().accept(new TLAExpressionScopingVisitor(builder));
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
		for(PGoTLAExpression expr : call.getArguments()) {
			expr.accept(new TLAExpressionScopingVisitor(builder));
		}
		return null;
	}

	@Override
	public Void visit(MacroCall macroCall) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public Void visit(With with) throws RuntimeException {
		with.getVariable().getValue().accept(new TLAExpressionScopingVisitor(builder));
		TLAScopeBuilder nested = builder.makeNestedScope();
		nested.defineLocal(with.getVariable().getName(), with.getVariable().getUID());
		for(Statement stmt : with.getBody()) {
			stmt.accept(new PlusCalStatementScopingVisitor(ctx, nested));
		}
		return null;
	}

	@Override
	public Void visit(Print print) throws RuntimeException {
		print.getValue().accept(new TLAExpressionScopingVisitor(builder));
		return null;
	}

	@Override
	public Void visit(Assert assert1) throws RuntimeException {
		assert1.getCondition().accept(new TLAExpressionScopingVisitor(builder));
		return null;
	}

	@Override
	public Void visit(Await await) throws RuntimeException {
		await.getCondition().accept(new TLAExpressionScopingVisitor(builder));
		return null;
	}

	@Override
	public Void visit(Goto goto1) throws RuntimeException {
		builder.reference(goto1.getTarget(), goto1.getUID());
		return null;
	}

}
