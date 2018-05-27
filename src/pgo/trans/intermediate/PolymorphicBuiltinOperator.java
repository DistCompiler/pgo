package pgo.trans.intermediate;

import pgo.errors.IssueContext;
import pgo.errors.TopLevelIssueContext;
import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Expression;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.type.*;
import pgo.scope.UID;
import pgo.trans.intermediate.BuiltinOperator.GoGenerator;
import pgo.trans.intermediate.BuiltinOperator.TypeConstraintGenerator;
import pgo.util.Origin;

import java.util.List;
import java.util.Map;

public class PolymorphicBuiltinOperator extends OperatorAccessor {

	private int argumentCount;
	private List<TypeConstraintGenerator> typeConstraintGenerators;
	private GoGenerator goGenerator;
	private UID uid;

	public PolymorphicBuiltinOperator(int argumentCount, List<TypeConstraintGenerator> typeConstraintGenerators,
			GoGenerator goGenerator) {
		this.uid = new UID();
		this.argumentCount = argumentCount;
		this.typeConstraintGenerators = typeConstraintGenerators;
		this.goGenerator = goGenerator;
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

	@Override
	public int getArgumentCount() {
		return argumentCount;
	}

	@Override
	public Expression generateGo(BlockBuilder builder, PGoTLAExpression origin, DefinitionRegistry registry,
			List<Expression> arguments, Map<UID, PGoType> typeMap, GlobalVariableStrategy globalStrategy) {
		return goGenerator.generate(builder, origin, registry, arguments, typeMap);
	}

	@Override
	public UID getUID() {
		return uid;
	}

}
