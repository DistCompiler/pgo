package pgo.trans.passes.type;

import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.type.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.Map;

public class MappingMacroReadBodyStatementTypeConstraintVisitor extends PlusCalStatementTypeConstraintVisitor {
	private PGoTypeVariable readValueTypeVariable;

	public MappingMacroReadBodyStatementTypeConstraintVisitor(IssueContext ctx, DefinitionRegistry registry,
	                                                          PGoTypeSolver solver, PGoTypeGenerator generator,
	                                                          Map<UID, PGoTypeVariable> mapping, UID readValueUID) {
		super(ctx, registry, solver, generator, mapping);
		this.readValueTypeVariable = generator.get();
		mapping.put(readValueUID, readValueTypeVariable);
	}

	@Override
	public Void visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		super.visit(modularPlusCalYield);
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				modularPlusCalYield,
				readValueTypeVariable,
				mapping.get(modularPlusCalYield.getExpression().getUID())));
		return null;
	}
}
