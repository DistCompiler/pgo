package pgo.trans.intermediate;

import pgo.errors.IssueContext;
import pgo.errors.TopLevelIssueContext;
import pgo.model.type.*;
import pgo.scope.UID;
import pgo.util.Origin;

import java.util.List;
import java.util.Map;

public class PolymorphicBuiltinOperator extends BuiltinOperator {

	protected List<TypeConstraintGenerator> typeConstraintGenerators;

	// disable super's constructor
	private PolymorphicBuiltinOperator(int argumentCount, TypeConstraintGenerator typeConstraintGenerator) {
		// this is here only to appease the Java compiler :(
		super(argumentCount, typeConstraintGenerator);
	}

	public PolymorphicBuiltinOperator(int argumentCount, List<TypeConstraintGenerator> typeConstraintGenerators) {
		// this is here only to appease the Java compiler :(
		super(argumentCount, typeConstraintGenerators.get(0));

		this.uid = new UID();
		this.argumentCount = argumentCount;
		this.typeConstraintGenerators = typeConstraintGenerators;
	}

	@Override
	public PGoType constrainTypes(IssueContext ctx, Origin origin, DefinitionRegistry registry, List<PGoType> argTypes, PGoTypeSolver solver, PGoTypeGenerator generator, Map<UID, PGoTypeVariable> mapping) {
		int i = 0;
		for (; i < typeConstraintGenerators.size(); i++) {
			TypeConstraintGenerator g = typeConstraintGenerators.get(i);
			PGoTypeSolver innerSolver = new PGoTypeSolver();
			PGoTypeGenerator innerGenerator = new PGoTypeGenerator("poly");
			IssueContext innerCtx = new TopLevelIssueContext();
			g.generate(innerCtx, origin, argTypes, innerSolver, innerGenerator);
			if (!innerCtx.hasErrors()) {
				break;
			}
		}
		if (i >= typeConstraintGenerators.size()) {
			ctx.error(new UnsatisfiablePolymorphicConstraintIssue(origin, argTypes));
			return generator.get();
		}
		return typeConstraintGenerators.get(i).generate(ctx, origin, argTypes, solver, generator);
	}

}
