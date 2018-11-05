package pgo.trans.passes.type;

import pgo.errors.IssueContext;
import pgo.model.pcal.PlusCalAssignment;
import pgo.model.pcal.PlusCalAssignmentPair;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.type.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.Map;
import java.util.Set;

public class ArchetypeBodyStatementTypeConstraintVisitor extends PlusCalStatementTypeConstraintVisitor {
	private Set<UID> paramsUIDs;

	public ArchetypeBodyStatementTypeConstraintVisitor(IssueContext ctx, DefinitionRegistry registry,
	                                                   PGoTypeSolver solver, PGoTypeGenerator generator,
	                                                   Map<UID, PGoTypeVariable> mapping, Set<UID> paramUIDs) {
		super(ctx, registry, solver, generator, mapping,
				new ArchetypeBodyExpressionTypeConstraintVisitor(registry, solver, generator, mapping, paramUIDs));
		this.paramsUIDs = paramUIDs;
	}

	@Override
	public Void visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		for (PlusCalAssignmentPair pair : plusCalAssignment.getPairs()) {
			TLAExpression lhs = pair.getLhs();
			if (lhs instanceof TLAGeneralIdentifier) {
				UID varUID = registry.followReference(lhs.getUID());
				if (paramsUIDs.contains(varUID)) {
					solver.addConstraint(new PGoTypeMonomorphicConstraint(
							pair,
							registry.getWrittenValueType(varUID),
							exprVisitor.wrappedVisit(pair.getRhs())));
					continue;
				}
			}
			solver.addConstraint(new PGoTypeMonomorphicConstraint(
                    pair, exprVisitor.wrappedVisit(lhs), exprVisitor.wrappedVisit(pair.getRhs())));
		}
		return null;
	}
}
