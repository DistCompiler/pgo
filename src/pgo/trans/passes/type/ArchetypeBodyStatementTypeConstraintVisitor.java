package pgo.trans.passes.type;

import pgo.model.pcal.PlusCalAssignment;
import pgo.model.pcal.PlusCalAssignmentPair;
import pgo.model.type.PGoTypeGenerator;
import pgo.model.type.PGoTypeMonomorphicConstraint;
import pgo.model.type.PGoTypeSolver;
import pgo.model.type.PGoTypeVariable;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.Map;
import java.util.Set;

public class ArchetypeBodyStatementTypeConstraintVisitor extends PlusCalStatementTypeConstraintVisitor {
	private final ArchetypeBodyExpressionTypeConstraintVisitor lhsVisitor;

	public ArchetypeBodyStatementTypeConstraintVisitor(DefinitionRegistry registry, PGoTypeSolver solver,
	                                                   PGoTypeGenerator generator, Map<UID, PGoTypeVariable> mapping,
	                                                   Set<UID> paramUIDs) {
		super(registry, solver, generator, mapping,
				new ArchetypeBodyExpressionTypeConstraintVisitor(
						registry, solver, generator, mapping, registry::getReadValueType, paramUIDs));
		this.lhsVisitor = new ArchetypeBodyExpressionTypeConstraintVisitor(
				registry, solver, generator, mapping, registry::getWrittenValueType, paramUIDs);
	}

	@Override
	public Void visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		for (PlusCalAssignmentPair pair : plusCalAssignment.getPairs()) {
			solver.addConstraint(new PGoTypeMonomorphicConstraint(
					pair, lhsVisitor.wrappedVisit(pair.getLhs()), exprVisitor.wrappedVisit(pair.getRhs())));
		}
		return null;
	}
}
