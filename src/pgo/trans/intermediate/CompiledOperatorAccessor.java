package pgo.trans.intermediate;

import java.util.List;
import java.util.Map;

import pgo.errors.IssueContext;
import pgo.model.tla.PGoTLAOpDecl;
import pgo.model.tla.PGoTLAOperatorDefinition;
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeConstraint;
import pgo.model.type.PGoTypeGenerator;
import pgo.model.type.PGoTypeSolver;
import pgo.model.type.PGoTypeVariable;
import pgo.scope.UID;
import pgo.util.Origin;

public class CompiledOperatorAccessor extends OperatorAccessor {

	private PGoTLAOperatorDefinition def;

	public CompiledOperatorAccessor(PGoTLAOperatorDefinition pGoTLAOperator) {
		this.def = pGoTLAOperator;
	}

	@Override
	public PGoType constrainTypes(IssueContext ctx, Origin origin, DefinitionRegistry registry, List<PGoType> args, PGoTypeSolver solver, PGoTypeGenerator generator,
	                              Map<UID, PGoTypeVariable> mapping) {
		// TODO argument-based polymorphism?
		List<PGoTLAOpDecl> defArgs = def.getArgs();
		for(int i = 0; i < defArgs.size(); ++i) {
			PGoTLAOpDecl arg = defArgs.get(i);
			if(arg.getType() == PGoTLAOpDecl.Type.ID) {
				PGoTypeVariable v = generator.get();
				mapping.put(arg.getUID(), v);
				solver.addConstraint(ctx, new PGoTypeConstraint(origin, v, args.get(i)));
			}else {
				// TODO: error
			}
		}
		PGoType result = new TLAExpressionTypeConstraintVisitor(ctx, registry, solver, generator, mapping)
				.wrappedVisit(def.getBody());
		return result;
	}

	@Override
	public int getArgumentCount() {
		return def.getArgs().size();
	}

}
