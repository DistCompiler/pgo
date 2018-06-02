package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.pcal.*;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.type.*;
import pgo.scope.UID;

public class PlusCalStatementTypeConstraintVisitor extends StatementVisitor<Void, RuntimeException> {

	private IssueContext ctx;
	private DefinitionRegistry registry;
	private PGoTypeSolver solver;
	private PGoTypeGenerator generator;
	private Map<UID, PGoTypeVariable> mapping;
	private TLAExpressionTypeConstraintVisitor exprVisitor;

	public PlusCalStatementTypeConstraintVisitor(IssueContext ctx, DefinitionRegistry registry, PGoTypeSolver solver, PGoTypeGenerator generator, Map<UID, PGoTypeVariable> mapping) {
		this.ctx = ctx;
		this.registry = registry;
		this.solver = solver;
		this.generator = generator;
		this.mapping = mapping;
		this.exprVisitor = new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping);
	}

	@Override
	public Void visit(LabeledStatements labeledStatements) throws RuntimeException {
		for (Statement stmt : labeledStatements.getStatements()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(While while1) throws RuntimeException {
		solver.addConstraint(new PGoTypeMonomorphicConstraint(while1, exprVisitor.wrappedVisit(while1.getCondition()), new PGoTypeBool(Collections.singletonList(while1))));
		for (Statement stmt : while1.getBody()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(If if1) throws RuntimeException {
		solver.addConstraint(new PGoTypeMonomorphicConstraint(if1, exprVisitor.wrappedVisit(if1.getCondition()), new PGoTypeBool(Collections.singletonList(if1))));
		for (Statement stmt : if1.getYes()) {
			stmt.accept(this);
		}
		for (Statement stmt : if1.getNo()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(Either either) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(Assignment assignment) throws RuntimeException {
		for(AssignmentPair pair : assignment.getPairs()) {
			solver.addConstraint(new PGoTypeMonomorphicConstraint(
					pair,
					exprVisitor.wrappedVisit(pair.getLhs()),
					exprVisitor.wrappedVisit(pair.getRhs())));
		}
		return null;
	}

	@Override
	public Void visit(Return return1) throws RuntimeException {
		// pass
		return null;
	}

	@Override
	public Void visit(Skip skip) throws RuntimeException {
		// pass
		return null;
	}

	@Override
	public Void visit(Call call) throws RuntimeException {
		Procedure proc = registry.findProcedure(call.getTarget());
		if (proc == null) {
			ctx.error(new ProcedureNotFoundIssue(call, call.getTarget()));
		}
		List<PGoType> callArgs = new ArrayList<>();
		for (PGoTLAExpression e : call.getArguments()) {
			TLAExpressionTypeConstraintVisitor v =
					new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping);
			e.accept(v);
			callArgs.add(mapping.get(e.getUID()));
		}
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				call,
				mapping.get(proc.getUID()),
				new PGoTypeProcedure(callArgs, Collections.singletonList(call))));
		return null;
	}

	@Override
	public Void visit(MacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(With with) throws RuntimeException {
		TypeInferencePass.constrainVariableDeclaration(registry, with.getVariable(), solver, generator, mapping);
		for (Statement stmt : with.getBody()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(Print print) throws RuntimeException {
		PGoTLAExpression expr = print.getValue();
		PGoType t = exprVisitor.wrappedVisit(expr);
		if (t instanceof PGoTypeUnrealizedTuple) {
			int probableSize = ((PGoTypeUnrealizedTuple) t).getProbableSize();
			List<PGoType> elemTypes = new ArrayList<>();
			for (int i = 0; i < probableSize; i++) {
				elemTypes.add(generator.get());
			}
			solver.addConstraint(new PGoTypeMonomorphicConstraint(expr, t, new PGoTypeTuple(elemTypes, Collections.singletonList(print))));
		}
		return null;
	}

	@Override
	public Void visit(Assert assert1) throws RuntimeException {
		solver.addConstraint(new PGoTypeMonomorphicConstraint(assert1, exprVisitor.wrappedVisit(assert1.getCondition()), new PGoTypeBool(Collections.singletonList(assert1))));
		return null;
	}

	@Override
	public Void visit(Await await) throws RuntimeException {
		solver.addConstraint(new PGoTypeMonomorphicConstraint(await, exprVisitor.wrappedVisit(await.getCondition()), new PGoTypeBool(Collections.singletonList(await))));
		return null;
	}

	@Override
	public Void visit(Goto goto1) throws RuntimeException {
		// pass
		return null;
	}

}
