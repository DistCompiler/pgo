package pgo.trans.intermediate;

import java.util.Map;

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
import pgo.model.type.PGoTypeBool;
import pgo.model.type.PGoTypeConstraint;
import pgo.model.type.PGoTypeGenerator;
import pgo.model.type.PGoTypeSolver;
import pgo.model.type.PGoTypeVariable;
import pgo.scope.UID;

public class PlusCalStatementTypeConstraintVisitor extends StatementVisitor<Void, RuntimeException> {
	
	private DefinitionRegistry registry;
	private PGoTypeSolver solver;
	private PGoTypeGenerator generator;
	private Map<UID, PGoTypeVariable> mapping;
	private TLAExpressionTypeConstraintVisitor exprVisitor;

	public PlusCalStatementTypeConstraintVisitor(DefinitionRegistry registry, PGoTypeSolver solver, PGoTypeGenerator generator, Map<UID, PGoTypeVariable> mapping) {
		this.registry = registry;
		this.solver = solver;
		this.generator = generator;
		this.mapping = mapping;
		this.exprVisitor = new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping);
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
		solver.accept(new PGoTypeConstraint(while1, exprVisitor.wrappedVisit(while1.getCondition()), PGoTypeBool.getInstance()));
		for(Statement stmt : while1.getBody()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(If if1) throws RuntimeException {
		solver.accept(new PGoTypeConstraint(if1, exprVisitor.wrappedVisit(if1.getCondition()), PGoTypeBool.getInstance()));
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
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Void visit(Assignment assignment) throws RuntimeException {
		solver.accept(new PGoTypeConstraint(
				assignment,
				exprVisitor.wrappedVisit(assignment.getLHS()),
				exprVisitor.wrappedVisit(assignment.getRHS())));
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
		// TODO: properly compile procedure calls
		return null;
	}

	@Override
	public Void visit(MacroCall macroCall) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public Void visit(With with) throws RuntimeException {
		TypeInferencePass.constrainVariableDecl(registry, with.getVariable(), solver, generator, mapping);
		for(Statement stmt : with.getBody()) {
			stmt.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(Print print) throws RuntimeException {
		exprVisitor.wrappedVisit(print.getValue());
		return null;
	}

	@Override
	public Void visit(Assert assert1) throws RuntimeException {
		solver.accept(new PGoTypeConstraint(assert1, exprVisitor.wrappedVisit(assert1.getCondition()), PGoTypeBool.getInstance()));
		return null;
	}

	@Override
	public Void visit(Await await) throws RuntimeException {
		solver.accept(new PGoTypeConstraint(await, exprVisitor.wrappedVisit(await.getCondition()), PGoTypeBool.getInstance()));
		return null;
	}

	@Override
	public Void visit(Goto goto1) throws RuntimeException {
		// pass
		return null;
	}

}
