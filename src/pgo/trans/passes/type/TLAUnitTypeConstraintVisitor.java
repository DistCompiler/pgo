package pgo.trans.passes.type;

import pgo.Unreachable;
import pgo.model.tla.*;
import pgo.model.type.PGoTypeGenerator;
import pgo.model.type.PGoTypeMonomorphicConstraint;
import pgo.model.type.PGoTypeSolver;
import pgo.model.type.PGoTypeVariable;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.Map;

public class TLAUnitTypeConstraintVisitor extends TLAUnitVisitor<Void, RuntimeException> {

	private DefinitionRegistry registry;
	private Map<UID, PGoTypeVariable> mapping;
	private PGoTypeGenerator generator;
	private PGoTypeSolver solver;

	public TLAUnitTypeConstraintVisitor(DefinitionRegistry registry, PGoTypeSolver solver,
	                                    PGoTypeGenerator generator, Map<UID, PGoTypeVariable> mapping) {
		this.registry = registry;
		this.solver = solver;
		this.generator = generator;
		this.mapping = mapping;
	}

	@Override
	public Void visit(TLAInstance pGoTLAInstance) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAFunctionDefinition pGoTLAFunctionDefinition) throws RuntimeException {
		UID id = pGoTLAFunctionDefinition.getName().getUID();
		PGoTypeVariable v;
		if (mapping.containsKey(id)) {
			v = mapping.get(id);
		} else {
			v = generator.get();
			mapping.put(id, v);
		}
		solver.addConstraint(
				new PGoTypeMonomorphicConstraint(
						pGoTLAFunctionDefinition,
						v,
						new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping)
								.wrappedVisit(pGoTLAFunctionDefinition.getFunction())));
		return null;
	}

	@Override
	public Void visit(TLAOperatorDefinition pGoTLAOperator) throws RuntimeException {
		// TODO: what about polymorphic operators?
		// i.e same operator called from two different places with different argument types
		for (TLAOpDecl arg : pGoTLAOperator.getArgs()) {
			if (!mapping.containsKey(arg.getName().getUID())) {
				mapping.put(arg.getName().getUID(), generator.get());
			}
		}
		new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping).wrappedVisit(pGoTLAOperator.getBody());
		return null;
	}

	@Override
	public Void visit(TLATheorem pGoTLATheorem) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAModule pGoTLAModule) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAVariableDeclaration pGoTLAVariableDeclaration) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAConstantDeclaration TLAConstantDeclaration) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAModuleDefinition pGoTLAModuleDefinition) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAAssumption TLAAssumption) throws RuntimeException {
		throw new Unreachable();
	}

}
