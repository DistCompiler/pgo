package pgo.trans.intermediate;

import pgo.model.golang.GoExpression;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.tla.TLAExpression;
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeGenerator;
import pgo.model.type.PGoTypeSolver;
import pgo.model.type.PGoTypeVariable;
import pgo.scope.UID;
import pgo.util.Derived;
import pgo.util.DerivedVisitor;
import pgo.util.Origin;

import java.util.List;
import java.util.Map;

public abstract class OperatorAccessor extends Derived {

	public abstract PGoType constrainTypes(Origin origin, DefinitionRegistry registry, List<PGoType> args, PGoTypeSolver solver,
	                                       PGoTypeGenerator generator, Map<UID, PGoTypeVariable> mapping);

	// TODO argument count mismatch
	public abstract int getArgumentCount();

	@Override
	public <T, E extends Throwable> T accept(DerivedVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public abstract UID getUID();

	public abstract GoExpression generateGo(GoBlockBuilder builder, TLAExpression origin, DefinitionRegistry registry,
											List<TLAExpression> args, Map<UID, PGoType> typeMap, GlobalVariableStrategy globalStrategy);

}
