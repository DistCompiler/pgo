package pgo.trans.intermediate;

import java.util.List;
import java.util.Map;

import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.GoExpression;
import pgo.model.tla.TLAExpression;
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeGenerator;
import pgo.model.type.PGoTypeSolver;
import pgo.model.type.PGoTypeVariable;
import pgo.scope.UID;
import pgo.util.Origin;

public class BuiltinOperator extends OperatorAccessor {

	public interface TypeConstraintGenerator {
		PGoType generate(Origin origin, List<PGoType> argTypes, PGoTypeSolver solver,
		                 PGoTypeGenerator generator);
	}
	public interface GoGenerator {
		GoExpression generate(GoBlockBuilder builder, TLAExpression expr, DefinitionRegistry registry,
							  List<TLAExpression> arguments, Map<UID, PGoType> typeMap, GlobalVariableStrategy globalStrategy);
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
	public PGoType constrainTypes(Origin origin, DefinitionRegistry registry, List<PGoType> argTypes, PGoTypeSolver solver,
	                              PGoTypeGenerator generator, Map<UID, PGoTypeVariable> mapping) {
		return typeConstraintGenerator.generate(origin, argTypes, solver, generator);
	}

	@Override
	public GoExpression generateGo(GoBlockBuilder builder, TLAExpression origin, DefinitionRegistry registry,
								   List<TLAExpression> args, Map<UID, PGoType> typeMap, GlobalVariableStrategy globalStrategy) {
		return goGenerator.generate(builder, origin, registry, args, typeMap, globalStrategy);
	}

}
