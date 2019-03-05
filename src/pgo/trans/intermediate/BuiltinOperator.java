package pgo.trans.intermediate;

import pgo.model.golang.GoExpression;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.tla.TLAExpression;
import pgo.model.type.Type;
import pgo.model.type.TypeGenerator;
import pgo.model.type.TypeSolver;
import pgo.model.type.TypeVariable;
import pgo.scope.UID;
import pgo.trans.passes.codegen.go.GlobalVariableStrategy;
import pgo.util.Origin;

import java.util.List;
import java.util.Map;

public class BuiltinOperator extends OperatorAccessor {

	public interface TypeConstraintGenerator {
		Type generate(Origin origin, List<Type> argTypes, TypeSolver solver,
		              TypeGenerator generator);
	}
	public interface GoGenerator {
		GoExpression generate(GoBlockBuilder builder, TLAExpression expr, DefinitionRegistry registry,
		                      List<TLAExpression> arguments, Map<UID, Type> typeMap, GlobalVariableStrategy globalStrategy);
	}

	private int argumentCount;
	private TypeConstraintGenerator typeConstraintGenerator;
	private UID uid;
	private GoGenerator goGenerator;

	public BuiltinOperator(int argumentCount, TypeConstraintGenerator typeConstraintGenerator, GoGenerator goGenerator) {
		this.uid = new UID();
		this.argumentCount = argumentCount;
		this.typeConstraintGenerator = typeConstraintGenerator;
		this.goGenerator = goGenerator;
	}

	public UID getUID() {
		return uid;
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
	public GoExpression generateGo(GoBlockBuilder builder, TLAExpression origin, DefinitionRegistry registry,
	                               List<TLAExpression> args, Map<UID, Type> typeMap, GlobalVariableStrategy globalStrategy) {
		return goGenerator.generate(builder, origin, registry, args, typeMap, globalStrategy);
	}

}
