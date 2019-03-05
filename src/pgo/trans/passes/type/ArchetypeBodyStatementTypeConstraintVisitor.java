package pgo.trans.passes.type;

import pgo.model.pcal.PlusCalAssignment;
import pgo.model.pcal.PlusCalAssignmentPair;
import pgo.model.type.TypeGenerator;
import pgo.model.type.constraint.MonomorphicConstraint;
import pgo.model.type.TypeSolver;
import pgo.model.type.TypeVariable;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.Map;
import java.util.Set;

public class ArchetypeBodyStatementTypeConstraintVisitor extends PlusCalStatementTypeConstraintVisitor {
	private final ArchetypeBodyExpressionTypeConstraintVisitor lhsVisitor;

	public ArchetypeBodyStatementTypeConstraintVisitor(DefinitionRegistry registry, TypeSolver solver,
	                                                   TypeGenerator generator, Map<UID, TypeVariable> mapping,
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
			solver.addConstraint(new MonomorphicConstraint(
					pair, lhsVisitor.wrappedVisit(pair.getLhs()), exprVisitor.wrappedVisit(pair.getRhs())));
		}
		return null;
	}
}
