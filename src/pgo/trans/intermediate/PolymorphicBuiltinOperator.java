package pgo.trans.intermediate;

import pgo.errors.IssueContext;
import pgo.errors.TopLevelIssueContext;
import pgo.model.type.*;
import pgo.scope.UID;
import pgo.util.Origin;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class PolymorphicBuiltinOperator extends BuiltinOperator {

	protected List<TypeConstraintGenerator> generators;

	// disable super's constructor
	private PolymorphicBuiltinOperator(int argumentCount, TypeConstraintGenerator typeConstraintGenerator) {
		// this is here only to appease the Java compiler :(
		super(argumentCount, typeConstraintGenerator);
	}

	public PolymorphicBuiltinOperator(int argumentCount, List<TypeConstraintGenerator> generators) {
		// this is here only to appease the Java compiler :(
		super(argumentCount, generators.get(0));

		this.uid = new UID();
		this.argumentCount = argumentCount;
		this.generators = generators;
	}

	@Override
	public PGoType constrainTypes(IssueContext ctx, Origin origin, DefinitionRegistry registry, List<PGoType> argTypes, PGoTypeSolver solver, PGoTypeGenerator generator, Map<UID, PGoTypeVariable> mapping) {
		int i = 0;
		for ( ; i < generators.size(); i++) {
			TypeConstraintGenerator g = generators.get(i);
			PGoTypeSolver innerSolver = new PGoTypeSolver();
			PGoTypeGenerator innerGenerator = new PGoTypeGenerator("poly");
			IssueContext innerCtx = new TopLevelIssueContext();
			g.generate(origin, argTypes, innerSolver, innerGenerator);
			innerSolver.unify(innerCtx);
			if (!innerCtx.hasErrors()) {
				break;
			}
		}
		if (i >= generators.size()) {
			ctx.error(new UnsatisfiablePolymorphicConstraintIssue(origin, argTypes));
			return generator.get();
		}
		return generators.get(i).generate(origin, argTypes, solver, generator);
	}

}
