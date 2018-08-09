package pgo.trans.intermediate;

import java.util.List;
import java.util.Set;

import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.pcal.*;
import pgo.model.pcal.PlusCalAssignment;
import pgo.model.tla.TLAExpression;
import pgo.modules.TLAModuleLoader;

public class PlusCalStatementScopingVisitor extends PlusCalStatementVisitor<Void, RuntimeException> {

	private IssueContext ctx;
	private TLAScopeBuilder builder;
	private DefinitionRegistry registry;
	private TLAModuleLoader loader;
	private Set<String> moduleRecursionSet;

	public PlusCalStatementScopingVisitor(IssueContext ctx, TLAScopeBuilder builder, DefinitionRegistry registry,
			TLAModuleLoader loader, Set<String> moduleRecursionSet) {
		this.ctx = ctx;
		this.builder = builder;
		this.registry = registry;
		this.loader = loader;
		this.moduleRecursionSet = moduleRecursionSet;
	}

	@Override
	public Void visit(PlusCalLabeledStatements labeledStatements) throws RuntimeException {
		for (PlusCalStatement stmt : labeledStatements.getStatements()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		plusCalWhile.getCondition().accept(new TLAExpressionScopingVisitor(builder, registry, loader, moduleRecursionSet));
		for (PlusCalStatement stmt : plusCalWhile.getBody()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalIf plusCalIf) throws RuntimeException {
		plusCalIf.getCondition().accept(new TLAExpressionScopingVisitor(builder, registry, loader, moduleRecursionSet));
		for (PlusCalStatement stmt : plusCalIf.getYes()) {
			stmt.accept(this);
		}
		for (PlusCalStatement stmt : plusCalIf.getNo()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalEither plusCalEither) throws RuntimeException {
		for (List<PlusCalStatement> list : plusCalEither.getCases()) {
			for (PlusCalStatement stmt : list) {
				stmt.accept(this);
			}
		}
		return null;
	}

	@Override
	public Void visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		for (PlusCalAssignmentPair pair : plusCalAssignment.getPairs()) {
			pair.getLhs().accept(new TLAExpressionScopingVisitor(builder, registry, loader, moduleRecursionSet));
			pair.getRhs().accept(new TLAExpressionScopingVisitor(builder, registry, loader, moduleRecursionSet));
		}
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
		for (TLAExpression expr : plusCalCall.getArguments()) {
			expr.accept(new TLAExpressionScopingVisitor(builder, null, null, null));
		}
		return null;
	}

	@Override
	public Void visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(PlusCalWith with) throws RuntimeException {
		with.getVariable().getValue().accept(new TLAExpressionScopingVisitor(builder, registry, loader, moduleRecursionSet));
		TLAScopeBuilder nested = builder.makeNestedScope();
		nested.defineLocal(with.getVariable().getName().getValue(), with.getVariable().getUID());
		registry.addLocalVariable(with.getVariable().getUID());
		for (PlusCalStatement stmt : with.getBody()) {
			stmt.accept(new PlusCalStatementScopingVisitor(ctx, nested, registry, loader, moduleRecursionSet));
		}
		return null;
	}

	@Override
	public Void visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		plusCalPrint.getValue().accept(new TLAExpressionScopingVisitor(builder, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		plusCalAssert.getCondition().accept(new TLAExpressionScopingVisitor(builder, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		plusCalAwait.getCondition().accept(new TLAExpressionScopingVisitor(builder, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		builder.reference(plusCalGoto.getTarget(), plusCalGoto.getUID());
		return null;
	}

}
