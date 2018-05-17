package pgo.trans.intermediate;


import pgo.model.tla.PGoTLAAssumption;
import pgo.model.tla.PGoTLAConstantDeclaration;
import pgo.model.tla.PGoTLAFunction;
import pgo.model.tla.PGoTLAFunctionDefinition;
import pgo.model.tla.PGoTLAIdentifier;
import pgo.model.tla.PGoTLAInstance;
import pgo.model.tla.PGoTLAModule;
import pgo.model.tla.PGoTLAModuleDefinition;
import pgo.model.tla.PGoTLAOpDecl;
import pgo.model.tla.PGoTLAOperatorDefinition;
import pgo.model.tla.PGoTLAQuantifierBound;
import pgo.model.tla.PGoTLATheorem;
import pgo.model.tla.PGoTLAUnitVisitor;
import pgo.model.tla.PGoTLAVariableDeclaration;

public class PGoTLAUnitScopingVisitor extends PGoTLAUnitVisitor<Void, RuntimeException> {

	ScopeInfoBuilder builder;

	public PGoTLAUnitScopingVisitor(ScopeInfoBuilder builder) {
		this.builder = builder;
	}

	@Override
	public Void visit(PGoTLAInstance pGoTLAInstance) throws RuntimeException {
		// TODO: support instantiating modules
		throw new RuntimeException("PGo does not support instantiating modules");
		/*for(PGoTLAInstance.Remapping remap : pGoTLAInstance.getRemappings()) {
			remap.getTo().accept(new PGoTLAExpressionScopingVisitor(builder.makeNestedScope()));
		}
		return null;*/
	}

	@Override
	public Void visit(PGoTLAFunctionDefinition pGoTLAFunctionDefinition) throws RuntimeException {
		if(pGoTLAFunctionDefinition.isLocal()) {
			builder.defineLocal(pGoTLAFunctionDefinition.getName().getId(), pGoTLAFunctionDefinition.getUID());
		}else {
			builder.defineGlobal(pGoTLAFunctionDefinition.getName().getId(), pGoTLAFunctionDefinition.getUID());
		}
		ScopeInfoBuilder argScope = builder.makeNestedScope();
		PGoTLAFunction fn = pGoTLAFunctionDefinition.getFunction();
		for(PGoTLAQuantifierBound qb : fn.getArguments()) {
			for(PGoTLAIdentifier id : qb.getIds()) {
				argScope.defineLocal(id.getId(), id.getUID());
			}
			qb.getSet().accept(new PGoTLAExpressionScopingVisitor(builder));
		}
		fn.getBody().accept(new PGoTLAExpressionScopingVisitor(argScope));
		return null;
	}

	@Override
	public Void visit(PGoTLAOperatorDefinition pGoTLAOperator) throws RuntimeException {
		if(pGoTLAOperator.isLocal()) {
			builder.defineLocal(pGoTLAOperator.getName().getId(), pGoTLAOperator.getUID());
		}else {
			builder.defineGlobal(pGoTLAOperator.getName().getId(), pGoTLAOperator.getUID());
		}
		ScopeInfoBuilder argScope = builder.makeNestedScope();
		for(PGoTLAOpDecl op : pGoTLAOperator.getArgs()) {
			argScope.defineLocal(op.getName().getId(), op.getName().getUID());
		}
		pGoTLAOperator.getBody().accept(new PGoTLAExpressionScopingVisitor(argScope));
		return null;
	}

	@Override
	public Void visit(PGoTLATheorem pGoTLATheorem) throws RuntimeException {
		pGoTLATheorem.getTheorem().accept(new PGoTLAExpressionScopingVisitor(builder));
		return null;
	}

	@Override
	public Void visit(PGoTLAModule pGoTLAModule) throws RuntimeException {
		// TODO: support nested modules
		throw new RuntimeException("PGo does not support nested modules");
	}

	@Override
	public Void visit(PGoTLAVariableDeclaration pGoTLAVariableDeclaration) throws RuntimeException {
		for(PGoTLAIdentifier id : pGoTLAVariableDeclaration.getVariables()) {
			builder.declare(id.getId(), id.getUID());
		}
		return null;
	}

	@Override
	public Void visit(PGoTLAConstantDeclaration pGoTLAConstantDeclaration) throws RuntimeException {
		for(PGoTLAOpDecl op : pGoTLAConstantDeclaration.getConstants()) {
			builder.declare(op.getName().getId(), op.getName().getUID());
		}
		return null;
	}

	@Override
	public Void visit(PGoTLAModuleDefinition pGoTLAModuleDefinition) throws RuntimeException {
		if(pGoTLAModuleDefinition.isLocal()) {
			builder.defineLocal(pGoTLAModuleDefinition.getName().getId(), pGoTLAModuleDefinition.getUID());
		}else {
			builder.defineGlobal(pGoTLAModuleDefinition.getName().getId(), pGoTLAModuleDefinition.getUID());
		}
		ScopeInfoBuilder argScope = builder.makeNestedScope();
		for(PGoTLAOpDecl op : pGoTLAModuleDefinition.getArgs()) {
			argScope.defineLocal(op.getName().getId(), op.getName().getUID());
		}
		PGoTLAInstance instance = pGoTLAModuleDefinition.getInstance();
		// TODO: check referenced module
		for(PGoTLAInstance.Remapping remap : instance.getRemappings()) {
			remap.getTo().accept(new PGoTLAExpressionScopingVisitor(argScope));
		}
		return null;
	}

	@Override
	public Void visit(PGoTLAAssumption pGoTLAAssumption) throws RuntimeException {
		pGoTLAAssumption.getAssumption().accept(new PGoTLAExpressionScopingVisitor(builder));
		return null;
	}

}
