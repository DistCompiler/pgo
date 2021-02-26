package pgo.trans.intermediate;

import pgo.InternalCompilerError;
import pgo.model.golang.GoExpression;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.tla.TLAExpression;
import pgo.model.type.Type;
import pgo.model.type.TypeGenerator;
import pgo.model.type.TypeSolver;
import pgo.model.type.TypeVariable;
import pgo.scope.UID;
import pgo.trans.passes.codegen.go.GlobalVariableStrategy;
import pgo.trans.passes.codegen.go.LocalVariableStrategy;
import pgo.util.Origin;

import java.util.List;
import java.util.Map;

public class BuiltinOperator extends OperatorAccessor {

	public interface TypeConstraintGenerator {
		Type generate(Origin origin, List<Type> argTypes, TypeSolver solver,
		              TypeGenerator generator);
	}
	public interface GoGenerator {
		GoExpression generate(GoBlockBuilder builder, TLAExpression expr, DefinitionRegistry registry, List<TLAExpression> arguments,
							  Map<UID, Type> typeMap, LocalVariableStrategy localSrtrategy, GlobalVariableStrategy globalStrategy);
	}

	private final int argumentCount;
	private final TypeConstraintGenerator typeConstraintGenerator;
	private final GoGenerator goGenerator;

	public BuiltinOperator(int argumentCount, TypeConstraintGenerator typeConstraintGenerator, GoGenerator goGenerator) {
		this.argumentCount = argumentCount;
		this.typeConstraintGenerator = typeConstraintGenerator;
		this.goGenerator = goGenerator;
	}

	public UID getUID() {
		throw new InternalCompilerError();
	}

	@Override
	public int getArgumentCount() {
		return argumentCount;
	}

	@Override
	public Type constrainTypes(Origin origin, DefinitionRegistry registry, List<Type> argTypes, TypeSolver solver,
	                           TypeGenerator generator, Map<UID, TypeVariable> mapping) {
		return typeConstraintGenerator.generate(origin, argTypes, solver, generator);
	}

	@Override
	public GoExpression generateGo(GoBlockBuilder builder, TLAExpression origin, DefinitionRegistry registry, List<TLAExpression> args,
								   Map<UID, Type> typeMap, LocalVariableStrategy localStrategy, GlobalVariableStrategy globalStrategy) {
		return goGenerator.generate(builder, origin, registry, args, typeMap, localStrategy, globalStrategy);
	}

}
