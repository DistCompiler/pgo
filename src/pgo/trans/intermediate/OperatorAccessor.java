package pgo.trans.intermediate;

import pgo.model.golang.GoExpression;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.tla.TLAExpression;
import pgo.model.type.*;
import pgo.model.type.TypeVariable;
import pgo.model.type.Type;
import pgo.scope.UID;
import pgo.trans.passes.codegen.go.GlobalVariableStrategy;
import pgo.util.Derived;
import pgo.util.DerivedVisitor;
import pgo.util.Origin;

import java.util.List;
import java.util.Map;

public abstract class OperatorAccessor extends Derived {

	public abstract Type constrainTypes(Origin origin, DefinitionRegistry registry, List<Type> args, TypeSolver solver,
	                                    TypeGenerator generator, Map<UID, TypeVariable> mapping);

	// TODO argument count mismatch
	public abstract int getArgumentCount();

	@Override
	public <T, E extends Throwable> T accept(DerivedVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public abstract UID getUID();

	public abstract GoExpression generateGo(GoBlockBuilder builder, TLAExpression origin, DefinitionRegistry registry,
	                                        List<TLAExpression> args, Map<UID, Type> typeMap, GlobalVariableStrategy globalStrategy);

}
