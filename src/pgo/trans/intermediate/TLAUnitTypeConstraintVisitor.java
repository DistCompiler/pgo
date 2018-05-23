package pgo.trans.intermediate;

import java.util.Map;

import pgo.errors.IssueContext;
import pgo.model.tla.PGoTLAAssumption;
import pgo.model.tla.PGoTLAConstantDeclaration;
import pgo.model.tla.PGoTLAFunctionDefinition;
import pgo.model.tla.PGoTLAInstance;
import pgo.model.tla.PGoTLAModule;
import pgo.model.tla.PGoTLAModuleDefinition;
import pgo.model.tla.PGoTLAOpDecl;
import pgo.model.tla.PGoTLAOperatorDefinition;
import pgo.model.tla.PGoTLATheorem;
import pgo.model.tla.PGoTLAUnitVisitor;
import pgo.model.tla.PGoTLAVariableDeclaration;
import pgo.model.type.PGoTypeConstraint;
import pgo.model.type.PGoTypeGenerator;
import pgo.model.type.PGoTypeSolver;
import pgo.model.type.PGoTypeVariable;
import pgo.scope.UID;

public class TLAUnitTypeConstraintVisitor extends PGoTLAUnitVisitor<Void, RuntimeException> {

	private IssueContext ctx;
	private DefinitionRegistry registry;
	private Map<UID, PGoTypeVariable> mapping;
	private PGoTypeGenerator generator;
	private PGoTypeSolver solver;

	public TLAUnitTypeConstraintVisitor(IssueContext ctx, DefinitionRegistry registry, PGoTypeSolver solver,
	                                    PGoTypeGenerator generator, Map<UID, PGoTypeVariable> mapping) {
		this.ctx = ctx;
		this.registry = registry;
		this.solver = solver;
		this.generator = generator;
		this.mapping = mapping;
	}

	@Override
	public Void visit(PGoTLAInstance pGoTLAInstance) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public Void visit(PGoTLAFunctionDefinition pGoTLAFunctionDefinition) throws RuntimeException {
		UID id = pGoTLAFunctionDefinition.getName().getUID();
		PGoTypeVariable v;
		if(mapping.containsKey(id)) {
			v = mapping.get(id);
		}else {
			v = generator.get();
			mapping.put(id, v);
		}
		solver.addConstraint(
				ctx,
				new PGoTypeConstraint(
						pGoTLAFunctionDefinition,
						v,
						new TLAExpressionTypeConstraintVisitor(ctx, registry, solver, generator, mapping)
						.wrappedVisit(pGoTLAFunctionDefinition.getFunction())));
		return null;
	}

	@Override
	public Void visit(PGoTLAOperatorDefinition pGoTLAOperator) throws RuntimeException {
		// TODO: what about polymorphic operators?
		// i.e same operator called from two different places with different argument types
		for(PGoTLAOpDecl arg : pGoTLAOperator.getArgs()) {
			if(!mapping.containsKey(arg.getUID())) {
				mapping.put(arg.getUID(), generator.get());
			}
		}
		new TLAExpressionTypeConstraintVisitor(ctx, registry, solver, generator, mapping).wrappedVisit(pGoTLAOperator.getBody());
		return null;
	}

	@Override
	public Void visit(PGoTLATheorem pGoTLATheorem) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public Void visit(PGoTLAModule pGoTLAModule) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public Void visit(PGoTLAVariableDeclaration pGoTLAVariableDeclaration) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public Void visit(PGoTLAConstantDeclaration pGoTLAConstantDeclaration) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public Void visit(PGoTLAModuleDefinition pGoTLAModuleDefinition) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public Void visit(PGoTLAAssumption pGoTLAAssumption) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

}
