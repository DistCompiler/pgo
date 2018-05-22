package pgo.trans.intermediate;

import java.util.List;
import java.util.Map;

import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeGenerator;
import pgo.model.type.PGoTypeSolver;
import pgo.model.type.PGoTypeVariable;
import pgo.scope.UID;

public class BuiltinOperator extends OperatorAccessor {
	
	public interface TypeConstraintGenerator{
		PGoType generate(List<PGoType> argTypes, PGoTypeSolver solver, PGoTypeGenerator generator);
	}
	
	private int argumentCount;
	private TypeConstraintGenerator typeConstraintGenerator;
	private UID uid;
	
	public BuiltinOperator(int argumentCount, TypeConstraintGenerator typeConstraintGenerator) {
		this.uid = new UID();
		this.argumentCount = argumentCount;
		this.typeConstraintGenerator = typeConstraintGenerator;
	}
	
	public UID getUID() {
		return uid;
	}
	
	@Override
	public int getArgumentCount() {
		return argumentCount;
	}
	
	@Override
	public PGoType constrainTypes(DefinitionRegistry registry, List<PGoType> argTypes, PGoTypeSolver solver,
			PGoTypeGenerator generator, Map<UID, PGoTypeVariable> mapping) {
		return typeConstraintGenerator.generate(argTypes, solver, generator);
	}

}
