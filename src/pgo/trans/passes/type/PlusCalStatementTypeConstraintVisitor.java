package pgo.trans.passes.type;

import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.type.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.ProcedureNotFoundIssue;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class PlusCalStatementTypeConstraintVisitor extends PlusCalStatementVisitor<Void, RuntimeException> {

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
	public Void visit(PlusCalLabeledStatements labeledStatements) throws RuntimeException {
		for (PlusCalStatement stmt : labeledStatements.getStatements()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		solver.addConstraint(new PGoTypeMonomorphicConstraint(plusCalWhile, exprVisitor.wrappedVisit(plusCalWhile.getCondition()), new PGoTypeBool(Collections.singletonList(plusCalWhile))));
		for (PlusCalStatement stmt : plusCalWhile.getBody()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalIf plusCalIf) throws RuntimeException {
		solver.addConstraint(new PGoTypeMonomorphicConstraint(plusCalIf, exprVisitor.wrappedVisit(plusCalIf.getCondition()), new PGoTypeBool(Collections.singletonList(plusCalIf))));
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
		for (List<PlusCalStatement> eitherCase : plusCalEither.getCases()) {
			for (PlusCalStatement statement : eitherCase) {
				statement.accept(this);
			}
		}
		return null;
	}

	@Override
	public Void visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		for(PlusCalAssignmentPair pair : plusCalAssignment.getPairs()) {
			// FIXME very broken, crashes anything that isn't tlagen mode
			// Matthew, pls help how does the type system work again?
			/*PGoType lhsTypeRoot = generator.get();
			PGoType lhsType = lhsTypeRoot;
			for(PlusCalLHSPart part : pair.getLhs().getParts()) {
				switch(part.getType()) {
					case INDEX:

						break;
					case DOT:
						lhsType = new PGoTypeMap(
								part.getArguments()
										.stream()
										.map(arg -> arg.accept(new TLAExpressionTypeConstraintVisitor(
												registry, solver, generator, mapping)))
										.collect(Collectors.toList()),
								lhsType,
								Collections.singletonList(part));
						break;
				}
			}*/
			solver.addConstraint(new PGoTypeMonomorphicConstraint(
					pair,
					exprVisitor.wrappedVisit(pair.getLhs().toExpression()),
					exprVisitor.wrappedVisit(pair.getRhs())));
		}
		return null;
	}

	@Override
	public Void visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		// pass
		return null;
	}

	@Override
	public Void visit(PlusCalSkip skip) throws RuntimeException {
		// pass
		return null;
	}

	@Override
	public Void visit(PlusCalCall plusCalCall) throws RuntimeException {
		PlusCalProcedure proc = registry.findProcedure(plusCalCall.getTarget());
		if (proc == null) {
			ctx.error(new ProcedureNotFoundIssue(plusCalCall, plusCalCall.getTarget()));
		}
		List<PGoType> callArgs = new ArrayList<>();
		for (TLAExpression e : plusCalCall.getArguments()) {
			TLAExpressionTypeConstraintVisitor v =
					new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping);
			e.accept(v);
			callArgs.add(mapping.get(e.getUID()));
		}
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				plusCalCall,
				mapping.get(proc.getUID()),
				new PGoTypeProcedure(callArgs, Collections.singletonList(plusCalCall))));
		return null;
	}

	@Override
	public Void visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(PlusCalWith with) throws RuntimeException {
		for(PlusCalVariableDeclaration decl : with.getVariables()) {
			TypeInferencePass.constrainVariableDeclaration(registry, decl, solver, generator, mapping);
		}
		for (PlusCalStatement stmt : with.getBody()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		exprVisitor.wrappedVisit(plusCalPrint.getValue());
		return null;
	}

	@Override
	public Void visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		solver.addConstraint(new PGoTypeMonomorphicConstraint(plusCalAssert, exprVisitor.wrappedVisit(plusCalAssert.getCondition()), new PGoTypeBool(Collections.singletonList(plusCalAssert))));
		return null;
	}

	@Override
	public Void visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		solver.addConstraint(new PGoTypeMonomorphicConstraint(plusCalAwait, exprVisitor.wrappedVisit(plusCalAwait.getCondition()), new PGoTypeBool(Collections.singletonList(plusCalAwait))));
		return null;
	}

	@Override
	public Void visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		// pass
		return null;
	}

}
