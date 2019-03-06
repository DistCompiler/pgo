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
	private final ArchetypeBodyLHSExpressionTypeConstraintVisitor lhsVisitor;

	public ArchetypeBodyStatementTypeConstraintVisitor(DefinitionRegistry registry, TypeSolver solver,
	                                                   TypeGenerator generator, Map<UID, TypeVariable> mapping,
	                                                   Set<UID> functionMappedParamUIDs, Set<UID> paramUIDs) {
		super(registry, solver, generator, mapping,
				new ArchetypeBodyExpressionTypeConstraintVisitor(
						registry, solver, generator, mapping, functionMappedParamUIDs, paramUIDs));
		this.lhsVisitor = new ArchetypeBodyLHSExpressionTypeConstraintVisitor(
				registry, solver, generator, mapping, functionMappedParamUIDs, paramUIDs);
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
